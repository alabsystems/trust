// targo trust report: verification report rendering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
#[cfg(test)]
use std::process::Command;
use std::time::Duration;

use serde::Serialize;
use sha2::{Digest, Sha256};
#[cfg(test)]
use trust_types::{AssuranceLevel, is_trust_vc_digest_bound_proof_certificate_artifact};
use trust_types::{
    Formula, FunctionProofReport, FunctionSummary, FunctionVerdict, HardenedAssuranceReport,
    HardenedBoundaryInventoryEntry, HardenedBoundaryInventoryRole, HardenedProfileReport,
    HardenedReportContext, HardenedSummaryReport, HardenedVcCategory,
    ObligationEvidenceProvenanceReport, ObligationOutcome, ObligationProofEvidenceReport,
    ObligationTransportEvidenceReport, ProofEvidence, ProofStrength, RuntimeCheckPolicy,
    SourceSpan, TransportEvidenceArtifact, TransportEvidenceDiagnostic,
    TransportEvidenceDiagnosticSeverity, TransportNativeTrustIrEvidence, TransportProofEvidence,
    TransportProofStatus, VcKind, VerificationCondition as TrustVc, VerificationResult as TrustVr,
    native_trust_ir_artifact_shape_is_publishable,
    native_trust_ir_artifact_shape_is_publishable_at_root,
};

use crate::types::{
    OutputFormat, VerificationOutcome, VerificationResult, structured_transport_evidence,
    transport_to_verification_result,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReportArtifact {
    Json,
    Ndjson,
    Html,
}

impl ReportArtifact {
    fn file_name(self) -> &'static str {
        match self {
            Self::Json => "report.json",
            Self::Ndjson => "report.ndjson",
            Self::Html => "report.html",
        }
    }

    #[cfg(test)]
    fn write_label(self) -> &'static str {
        match self {
            Self::Json => "JSON report",
            Self::Ndjson => "NDJSON report",
            Self::Html => "HTML report",
        }
    }
}

const PROOF_UNSAFE_MEMORY_REPORT_SCHEMA: &str = "trust.proof-unsafe-memory-report.v1";
const PROOF_UNSAFE_MEMORY_COMMAND: &str = "targo trust report --unsafe-memory";
const PROOF_UNSAFE_MEMORY_WRAPPER_FILE: &str = "unsafe-memory.json";
const MAX_REPORT_ARTIFACT_STORE_BYTES: u64 = 512 * 1024 * 1024;
const MAX_INLINE_REPORT_ARTIFACT_BYTES: u64 = 48 * 1024 * 1024;

struct BoundedReportBytes {
    bytes: Vec<u8>,
    limit: usize,
}

impl Write for BoundedReportBytes {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let next_len = self.bytes.len().checked_add(bytes.len()).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "canonical report size overflow")
        })?;
        if next_len > self.limit {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("canonical report exceeds the {}-byte saved-report limit", self.limit),
            ));
        }
        self.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn serialize_json_bounded(value: &impl Serialize, limit: usize) -> io::Result<Vec<u8>> {
    let mut output = BoundedReportBytes { bytes: Vec::new(), limit };
    serde_json::to_writer(&mut output, value)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    Ok(output.bytes)
}

fn serialize_canonical_report_bounded(
    report: &trust_types::JsonProofReport,
) -> io::Result<Vec<u8>> {
    serialize_json_bounded(report, crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES)
}

#[derive(Debug, Clone)]
pub(crate) struct UnsafeMemoryReportRequest {
    pub(crate) repo_root: PathBuf,
}

impl UnsafeMemoryReportRequest {
    pub(crate) fn new(repo_root: PathBuf) -> Self {
        Self { repo_root }
    }
}

#[derive(Debug, Clone, Serialize)]
struct ProofUnsafeMemoryReport<'a> {
    schema: &'static str,
    candidate_commit: String,
    candidate_tree: String,
    repo_dirty: bool,
    producer: ProofUnsafeMemoryProducer,
    proof_report_path: &'a str,
    proof_report_hash: String,
    coverage: ProofUnsafeMemoryCoverage,
    unsupported: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
struct ProofUnsafeMemoryProducer {
    command: &'static str,
    native: bool,
}

#[derive(Debug, Clone, Copy, Serialize)]
struct ProofUnsafeMemoryCoverage {
    unsafe_blocks_total: u64,
    unsafe_blocks_proved: u64,
    unsafe_operations_total: u64,
    unsafe_operations_proved: u64,
    memory_obligations_total: u64,
    memory_obligations_proved: u64,
}

/// A non-verification diagnostic line captured from compiler output.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct CompilerDiagnostic {
    pub(crate) level: String,
    pub(crate) message: String,
}

/// Config info included in the report.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ReportConfig {
    pub(crate) level: String,
    pub(crate) timeout_ms: u64,
    pub(crate) function_budget_ms: u64,
    pub(crate) enabled: bool,
    pub(crate) hardened: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) trust_profile: Option<String>,
}

pub(crate) use trust_types::{
    CertifiedTestExecutableReport, CertifiedTestExecutionCompletionScope,
    CertifiedTestExecutionPhaseState, CertifiedTestExecutionReport,
};

/// Summary report of a verification run.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct VerificationReport {
    /// Truthful subject identity for the canonical proof report. Cargo mode
    /// supplies one authenticated target identity or an explicit aggregate;
    /// single-file/test producers use an explicit source/unscoped label.
    pub(crate) report_subject: String,
    pub(crate) success: bool,
    pub(crate) exit_code: i32,
    pub(crate) proved: usize,
    pub(crate) failed: usize,
    /// Genuine unknowns only (excludes explicit `assumption:*` and design-mandate
    /// rows, which are partitioned into `assumed`/`mandated`). See
    /// `partition_outcome_counts`.
    pub(crate) unknown: usize,
    pub(crate) runtime_checked: usize,
    /// Explicit `assumption:*` ledger rows (green front door, Stage 2).
    #[serde(default)]
    pub(crate) assumed: usize,
    /// Compiler design-mandate rows (green front door, Stage 2).
    #[serde(default)]
    pub(crate) mandated: usize,
    /// Trust (T9 contract-panic): `contract-panic:*` rows — annotated,
    /// message-matched intentional fail-closed panics. Always rendered in the
    /// summary line (even when 0) so a pass conditional on one is never silent.
    #[serde(default)]
    pub(crate) contract_panics: usize,
    /// Trust (verify-cache): obligations replayed from the persistent proof cache
    /// (sum of per-function `FunctionTransportResult::cached`). Informational
    /// only — these obligations are also counted conservatively as `unknown` in
    /// the per-obligation `results` (no proof credit); this drives the report's
    /// cache hit-rate line without altering any verdict.
    pub(crate) cached: usize,
    pub(crate) total: usize,
    pub(crate) results: Vec<VerificationResult>,
    /// Authenticated function identities whose compiler transport contained the
    /// exact structural zero-obligation inventory row. These are not proof
    /// obligations and never contribute proof credit; they preserve the typed
    /// function inventory after those synthetic rows are elided.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) zero_obligation_functions: Vec<String>,
    pub(crate) compiler_diagnostics: Vec<CompilerDiagnostic>,
    pub(crate) duration_ms: u64,
    pub(crate) config: ReportConfig,
    /// Trust (assumption ledger): crate-scope dependency assumptions from the
    /// dep-TCB set (crate mode only; empty in single-file mode). Function-scope
    /// entries are derived from `assumption:<tag>` transport rows at report
    /// build time.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub(crate) dep_assumptions: Vec<trust_types::AssumptionEntry>,
    /// Trust (green front door, Stage 2): the tiered exit-code gate decision for
    /// this run, mirrored into `report.json` as `verification_gate`. Filled by
    /// `run_compiler` after the hardened/missing-json success flips.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) gate: Option<trust_types::VerificationGateReport>,
    /// Trust (assertion-grade coverage, roadmap §4.1): the run's verification-
    /// coverage accounting from the compiler's `coverage_summary` transport
    /// row(s), also mirrored into `report.json` under
    /// `verification_gate.coverage`. `None` = the compiler emitted no coverage
    /// row (an older toolchain): coverage UNKNOWN — reported as such, never a
    /// failure on absence alone. `coverage_complete == false` is fail-closed:
    /// the gate was capped at INCONCLUSIVE (`apply_coverage_gate`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) coverage: Option<trust_types::VerificationCoverage>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) test_execution: Option<CertifiedTestExecutionReport>,
    /// Observational projection of Cargo's exact declared proof frontier and
    /// the units that completed and emitted coverage. Populated only for Cargo
    /// crate-mode runs and never used as live proof authority.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) cargo_proof_inventory: Option<trust_types::CargoProofInventoryReport>,
    /// Explicit private root containing path-backed proof materializations for
    /// this run. This is runtime authority only and is never serialized.
    #[serde(skip)]
    pub(crate) proof_artifact_root: Option<PathBuf>,
    /// Non-serializable, same-process authority for the exact compiler rows
    /// captured from the authenticated Cargo/direct transport channel. A JSON
    /// report, raw parser result, or reconstructed DTO never carries this.
    #[serde(skip)]
    pub(crate) live_transport_authority: Option<LiveTransportAuthority>,
}

/// Private receipt over one completed compiler session's exact result vector.
///
/// This is deliberately not serializable. The random compiler session is not a
/// signature and the row digests are not proofs; authority comes from minting
/// this value only after Targo's protected child channel and scope/session
/// checks complete. The digests make later mutation, reordering, or evidence
/// donation invalidate that live authority before report publication.
#[derive(Debug, Clone)]
pub(crate) struct LiveTransportAuthority {
    report_subject: String,
    verification_session: String,
    row_receipts: Vec<[u8; 32]>,
    zero_obligation_functions: Vec<String>,
    complete_report_receipt: Option<[u8; 32]>,
    canonical_report_receipt: Option<[u8; 32]>,
    sealed_canonical_report: Option<trust_types::JsonProofReport>,
    sealed_canonical_bytes: Option<Vec<u8>>,
}

struct AuthorizedRows<'a> {
    results: &'a [VerificationResult],
}

impl AuthorizedRows<'_> {
    fn authorizes_row(&self, index: usize, result: &VerificationResult) -> bool {
        self.results.get(index).is_some_and(|authorized| std::ptr::eq(authorized, result))
    }

    fn authorizes_proved_row(&self, index: usize, result: &VerificationResult) -> bool {
        self.authorizes_row(index, result)
            && result.outcome.is_proved()
            && compiler_claim_digest(result).is_some()
            && !matches!(report_vc_kind(result), VcKind::UnsupportedMir { .. })
    }
}

impl LiveTransportAuthority {
    pub(crate) fn capture_authenticated_projection(
        report_subject: &str,
        verification_session: &str,
        authenticated_compiler_results: &[VerificationResult],
        publication_results: &[VerificationResult],
        materialization_root: Option<&Path>,
    ) -> Option<Self> {
        let mut expected_publication = authenticated_compiler_results.to_vec();
        crate::types::normalize_authenticated_results_for_publication(
            &mut expected_publication,
            materialization_root,
        );
        if serde_json::to_vec(&expected_publication).ok()?
            != serde_json::to_vec(publication_results).ok()?
        {
            return None;
        }
        let zero_obligation_functions =
            crate::types::authenticated_zero_obligation_inventory(authenticated_compiler_results);
        if publication_results
            .iter()
            .any(|result| zero_obligation_functions.binary_search(&result.function).is_ok())
        {
            return None;
        }
        Self::capture_exact(
            report_subject,
            verification_session,
            publication_results,
            zero_obligation_functions,
        )
    }

    fn capture_exact(
        report_subject: &str,
        verification_session: &str,
        results: &[VerificationResult],
        zero_obligation_functions: Vec<String>,
    ) -> Option<Self> {
        if report_subject.trim().is_empty() || !trust_types::digest::is_stable_sha256_hex(verification_session) {
            return None;
        }
        let row_receipts = results
            .iter()
            .enumerate()
            .map(|(index, result)| {
                live_transport_row_receipt(report_subject, verification_session, index, result)
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Self {
            report_subject: report_subject.to_string(),
            verification_session: verification_session.to_string(),
            row_receipts,
            zero_obligation_functions,
            complete_report_receipt: None,
            canonical_report_receipt: None,
            sealed_canonical_report: None,
            sealed_canonical_bytes: None,
        })
    }

    /// Replace path-backed materializations with their exact bounded bytes
    /// without widening authority.  The old row receipts are validated first;
    /// inlining then decodes each artifact beneath the already-authenticated
    /// root and checks its declared digest.  Only that transactional transform
    /// may rebind this private authority to the resulting self-contained rows.
    fn inline_authenticated_rows(
        &mut self,
        report_subject: &str,
        results: &mut [VerificationResult],
        artifact_root: &Path,
    ) -> bool {
        if self.validate_rows(report_subject, results).is_none() {
            return false;
        }

        let mut inlined = results.to_vec();
        if inline_verification_result_artifacts(&mut inlined, artifact_root).is_err() {
            return false;
        }
        let row_receipts = inlined
            .iter()
            .enumerate()
            .map(|(index, result)| {
                live_transport_row_receipt(
                    report_subject,
                    &self.verification_session,
                    index,
                    result,
                )
            })
            .collect::<Option<Vec<_>>>();
        let Some(row_receipts) = row_receipts else {
            return false;
        };

        results.clone_from_slice(&inlined);
        self.row_receipts = row_receipts;
        self.complete_report_receipt = None;
        self.canonical_report_receipt = None;
        self.sealed_canonical_report = None;
        self.sealed_canonical_bytes = None;
        true
    }

    fn validate_rows<'a>(
        &'a self,
        report_subject: &str,
        results: &'a [VerificationResult],
    ) -> Option<AuthorizedRows<'a>> {
        if self.report_subject != report_subject
            || !trust_types::digest::is_stable_sha256_hex(&self.verification_session)
            || self.row_receipts.len() != results.len()
        {
            return None;
        }
        for (index, result) in results.iter().enumerate() {
            let actual = live_transport_row_receipt(
                report_subject,
                &self.verification_session,
                index,
                result,
            )?;
            if self.row_receipts[index] != actual {
                return None;
            }
        }
        Some(AuthorizedRows { results })
    }

    fn seal_complete_report(
        &mut self,
        report_subject: &str,
        results: &[VerificationResult],
        zero_obligation_functions: &[String],
        serialized_report: &[u8],
        artifact_root: Option<&Path>,
    ) -> bool {
        if self.validate_rows(report_subject, results).is_none()
            || self.zero_obligation_functions != zero_obligation_functions
        {
            return false;
        }
        self.complete_report_receipt = Some(complete_report_receipt(
            report_subject,
            &self.verification_session,
            serialized_report,
            artifact_root,
        ));
        true
    }

    fn validate_complete_report<'a>(
        &'a self,
        report_subject: &str,
        results: &'a [VerificationResult],
        zero_obligation_functions: &[String],
        serialized_report: &[u8],
        artifact_root: Option<&Path>,
    ) -> Option<AuthorizedRows<'a>> {
        let rows = self.validate_rows(report_subject, results)?;
        if self.zero_obligation_functions != zero_obligation_functions {
            return None;
        }
        let expected = self.complete_report_receipt?;
        let actual = complete_report_receipt(
            report_subject,
            &self.verification_session,
            serialized_report,
            artifact_root,
        );
        (actual == expected).then_some(rows)
    }

    fn seal_canonical_report(
        &mut self,
        report_subject: &str,
        report: trust_types::JsonProofReport,
        serialized_report: Vec<u8>,
    ) -> bool {
        if self.report_subject != report_subject || self.complete_report_receipt.is_none() {
            return false;
        }
        self.canonical_report_receipt = Some(length_bound_sha256(
            "targo.canonical-publication-report.v1",
            &[report_subject.as_bytes(), self.verification_session.as_bytes(), &serialized_report],
        ));
        self.sealed_canonical_report = Some(report);
        self.sealed_canonical_bytes = Some(serialized_report);
        true
    }

    fn validate_canonical_report(&self, report_subject: &str, serialized_report: &[u8]) -> bool {
        let Some(expected) = self.canonical_report_receipt else {
            return false;
        };
        let actual = length_bound_sha256(
            "targo.canonical-publication-report.v1",
            &[report_subject.as_bytes(), self.verification_session.as_bytes(), serialized_report],
        );
        actual == expected
    }

    fn sealed_canonical_publication(&self) -> Option<(&trust_types::JsonProofReport, &[u8])> {
        let report = self.sealed_canonical_report.as_ref()?;
        let serialized = self.sealed_canonical_bytes.as_deref()?;
        self.validate_canonical_report(&self.report_subject, serialized)
            .then_some((report, serialized))
    }
}

fn compiler_claim_digest(result: &VerificationResult) -> Option<String> {
    let evidence = structured_transport_evidence(result)?;
    evidence.claim_digest_sha256.filter(|digest| trust_types::digest::is_stable_sha256_hex(digest))
}


fn live_transport_row_receipt(
    report_subject: &str,
    verification_session: &str,
    index: usize,
    result: &VerificationResult,
) -> Option<[u8; 32]> {
    let row = serde_json::to_vec(result).ok()?;
    let index = (index as u64).to_be_bytes();
    Some(length_bound_sha256(
        "targo.live-compiler-transport-row.v1",
        &[report_subject.as_bytes(), verification_session.as_bytes(), &index, &row],
    ))
}

fn length_bound_sha256(domain: &str, parts: &[&[u8]]) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(b"targo.digest-frame.v1");
    digest.update((domain.len() as u64).to_be_bytes());
    digest.update(domain.as_bytes());
    digest.update((parts.len() as u64).to_be_bytes());
    for part in parts {
        digest.update((part.len() as u64).to_be_bytes());
        digest.update(part);
    }
    digest.finalize().into()
}

fn complete_report_receipt(
    report_subject: &str,
    verification_session: &str,
    serialized_report: &[u8],
    artifact_root: Option<&Path>,
) -> [u8; 32] {
    let artifact_root = artifact_root
        .map_or_else(Vec::new, |path| path.as_os_str().to_string_lossy().as_bytes().to_vec());
    length_bound_sha256(
        "targo.complete-publication-state.v1",
        &[
            report_subject.as_bytes(),
            verification_session.as_bytes(),
            serialized_report,
            &artifact_root,
        ],
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct HardenedProofGateFailure {
    pub(crate) hardened_obligations: usize,
    pub(crate) proof_evidence_entries: usize,
}

/// Same-process view of the exact canonical report covered by both the final
/// internal publication seal and the canonical projection receipt.
///
/// The field and constructor stay private to this module: callers can consume
/// a live report only after [`VerificationReport`] has revalidated those two
/// receipts.  Saved JSON can never construct this capability.
pub(crate) struct LiveCanonicalReport {
    report: trust_types::JsonProofReport,
}

/// Render the exact active Cargo Units that were outside the authenticated
/// proof frontier. This deliberately uses Cargo's source-qualified package ID
/// and invocation-local Unit index: display names alone are not identities in
/// a graph containing multiple versions or modes of the same target.
pub(crate) fn cargo_active_exclusion_labels(
    inventory: Option<&trust_types::CargoProofInventoryReport>,
) -> Vec<String> {
    inventory
        .into_iter()
        .flat_map(|inventory| &inventory.excluded_active_units)
        .map(cargo_exclusion_unit_label)
        .collect()
}

/// Source-qualified, invocation-local label for one excluded active Cargo Unit.
fn cargo_exclusion_unit_label(unit: &trust_types::CargoProofUnitReport) -> String {
    format!(
        "package_id={:?} package_name={:?} target={:?} target_kinds={:?} compile_target={:?} compile_target_spec_sha256={:?} unit_index={} mode={:?} proof_role={:?} graph_role={:?} reason={:?}",
        unit.package_id,
        unit.package_name,
        unit.target_name,
        unit.target_kinds,
        unit.compile_target,
        unit.compile_target_spec_sha256,
        unit.proof_unit_index,
        unit.proof_unit_mode,
        unit.proof_unit_role,
        unit.graph_role,
        unit.exclusion_reason.as_deref().unwrap_or("missing-exclusion-reason"),
    )
}

/// Active Cargo exclusions that must fail the whole-crate verification gate:
/// exactly those excluded active Units that are NOT admitted as resolved
/// dependency-TCB trust assumptions.
///
/// A Unit admitted to the dependency-TCB ledger is trusted-assumed and recorded
/// verbatim as a `Conditional` assumption in the report; it is never claimed
/// proved, and by itself does not render the whole-crate proof incomplete.
/// Every exclusion the ledger cannot resolve into an explicit trust scope
/// (unsupported/policy-inconsistent, or missing its reason) remains here and
/// keeps the gate fail-closed.
pub(crate) fn cargo_gate_failing_exclusion_labels(
    inventory: Option<&trust_types::CargoProofInventoryReport>,
) -> Vec<String> {
    inventory
        .into_iter()
        .flat_map(|inventory| {
            let include_dependencies = inventory.include_dependencies;
            inventory.excluded_active_units.iter().filter_map(move |unit| {
                if crate::dep_tcb::report_unit_is_dep_tcb_admitted(include_dependencies, unit) {
                    None
                } else {
                    Some(cargo_exclusion_unit_label(unit))
                }
            })
        })
        .collect()
}

/// Whether the proof frontier carries any exclusion that must fail the
/// whole-crate gate — an excluded active Unit NOT admitted as a resolved
/// dependency-TCB trust assumption. dep-TCB-admitted exclusions (third-party
/// dependency / build-script / etc.) are recorded verbatim as `Conditional`
/// assumptions in the report ledger, so they are trusted-assumed, never claimed
/// proved, and do not by themselves render the whole-crate proof incomplete.
/// Every unresolved exclusion still forces fail-closed here.
pub(crate) fn cargo_has_gate_failing_exclusions(
    inventory: Option<&trust_types::CargoProofInventoryReport>,
) -> bool {
    inventory.is_some_and(|inventory| {
        inventory.excluded_active_units.iter().any(|unit| {
            !crate::dep_tcb::report_unit_is_dep_tcb_admitted(inventory.include_dependencies, unit)
        })
    })
}

impl LiveCanonicalReport {
    /// Canonical rows for the focused-query workflow. The opaque capability is
    /// still held by the caller for the entire borrow.
    pub(crate) fn for_focused_query(&self) -> &trust_types::JsonProofReport {
        &self.report
    }

    /// Canonical rows for immediate Trust-on-Trust frontier reduction. The
    /// reducer must retain only derived measurements, never this report DTO.
    pub(crate) fn for_self_improve_reduction(&self) -> &trust_types::JsonProofReport {
        &self.report
    }
}

impl VerificationReport {
    fn serialized_publication_state(&self) -> Option<Vec<u8>> {
        serialize_json_bounded(self, crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES).ok()
    }

    /// Seal the final run-level publication state after outcome, coverage,
    /// hardened, missing-transport, gate, and exit decisions are fixed.  Row
    /// receipts alone are intentionally insufficient for a crate-level
    /// Verified/PASS claim.
    pub(crate) fn seal_for_publication(&mut self) -> bool {
        // Pathnames are mutable ambient state and cannot survive inside a
        // final publication capability. Validate the old row receipts, then
        // transactionally decode every materialization beneath the captured
        // root against its declared digest and rebind only those exact bytes.
        if let Some(artifact_root) = self.proof_artifact_root.clone() {
            let Some(authority) = self.live_transport_authority.as_mut() else {
                return false;
            };
            if !authority.inline_authenticated_rows(
                &self.report_subject,
                &mut self.results,
                &artifact_root,
            ) {
                return false;
            }
            self.proof_artifact_root = None;
        }

        let Some(serialized) = self.serialized_publication_state() else {
            return false;
        };
        let Some(authority) = self.live_transport_authority.as_mut() else {
            return false;
        };
        if !authority.seal_complete_report(
            &self.report_subject,
            &self.results,
            &self.zero_obligation_functions,
            &serialized,
            self.proof_artifact_root.as_deref(),
        ) {
            return false;
        }

        // Bind the exact canonical projection too. This rejects any internal
        // PASS whose rows cannot be attached one-for-one to the report that
        // users actually see, before terminal/JSON/HTML output begins.
        let canonical = self.to_trust_report();
        if !self.canonical_report_matches_internal_state(&canonical) {
            if let Some(authority) = self.live_transport_authority.as_mut() {
                authority.complete_report_receipt = None;
                authority.canonical_report_receipt = None;
                authority.sealed_canonical_report = None;
                authority.sealed_canonical_bytes = None;
            }
            return false;
        }
        let Ok(serialized_canonical) = serialize_canonical_report_bounded(&canonical) else {
            return false;
        };
        self.live_transport_authority.as_mut().is_some_and(|authority| {
            authority.seal_canonical_report(&self.report_subject, canonical, serialized_canonical)
        })
    }

    /// Revalidate the complete run state and canonical projection, then expose
    /// an opaque same-process capability for proof-consuming workflows. This is
    /// deliberately separate from saved-report deserialization: once the live
    /// compiler authority is dropped, no serialized shape can recreate it.
    pub(crate) fn sealed_canonical_report(&self) -> io::Result<LiveCanonicalReport> {
        let active_exclusions = cargo_active_exclusion_labels(self.cargo_proof_inventory.as_ref());
        if !active_exclusions.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "live proof consumption requires an exclusion-free Cargo proof frontier; {} active Cargo Unit(s) were excluded: {}",
                    active_exclusions.len(),
                    active_exclusions.join("; "),
                ),
            ));
        }
        if self.complete_authorized_rows().is_none() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "live canonical report requires a valid final publication seal",
            ));
        }
        let report = self
            .live_transport_authority
            .as_ref()
            .and_then(LiveTransportAuthority::sealed_canonical_publication)
            .map(|(report, _)| report.clone())
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    "live canonical report no longer matches its retained canonical projection receipt",
                )
            })?;
        Ok(LiveCanonicalReport { report })
    }

    fn canonical_report_matches_internal_state(
        &self,
        report: &trust_types::JsonProofReport,
    ) -> bool {
        let Some(expected_unknown) = self
            .unknown
            .checked_add(self.assumed)
            .and_then(|value| value.checked_add(self.contract_panics))
        else {
            return false;
        };
        // The canonical projection recognizes a design mandate ONLY on an
        // AUTHORIZED row (`authorizes_row && transport_design_mandate`, see
        // `to_trust_report`): without live row authority the transport bit is
        // untrusted and the row conservatively classifies as unknown. Apply the
        // IDENTICAL gate to the expected counts, or a fail-closed run (e.g. a
        // strict compile abort, which has no complete authorized report) with a
        // mandate row would always mismatch here — turning the honest
        // developer-failure exit into a seal failure (exit 2).
        let authorized_mandated = {
            let authority = self.complete_authorized_rows();
            self.results
                .iter()
                .enumerate()
                .filter(|(index, result)| {
                    authority
                        .as_ref()
                        .is_some_and(|authority| authority.authorizes_row(*index, result))
                        && transport_design_mandate(result)
                })
                .count()
        };
        let Some(unauthorized_mandated) = self.mandated.checked_sub(authorized_mandated) else {
            // The authorized subset can never outnumber the raw partition.
            // Treat any internal accounting drift as a seal failure instead of
            // hiding it behind saturating arithmetic.
            return false;
        };
        let Some(expected_unknown) = expected_unknown.checked_add(unauthorized_mandated) else {
            return false;
        };
        let expected_mandated = authorized_mandated;
        let summary = &report.summary;
        if report.verification_gate != self.gate
            || report.cargo_proof_inventory != self.cargo_proof_inventory
            || summary.total_obligations != self.total
            || summary.total_proved != self.proved
            || summary.total_failed != self.failed
            || summary.total_runtime_checked != self.runtime_checked
            || summary.total_design_requirements != expected_mandated
            || summary.total_unknown != expected_unknown
            || summary.total_unattributed_failed != 0
            || summary.total_unattributed_unknown != 0
            || summary.total_unattributed_proved != 0
        {
            return false;
        }

        let Some(gate) = report.verification_gate.as_ref() else {
            return false;
        };
        let gate_success =
            gate.exit_code == 0 && matches!(gate.decision.as_str(), "pass" | "conditional-pass");
        // Only exclusions NOT admitted to the dependency-TCB ledger cap the
        // crate: an admitted third-party dep/build-script is a recorded
        // `Conditional` assumption, not a proof gap, so it may coexist with a
        // success/pass verdict. Any unresolved exclusion still forces
        // fail-closed here (success and pass are rejected, verdict must be
        // Inconclusive/HasViolations).
        let has_gate_failing_cargo_exclusions =
            cargo_has_gate_failing_exclusions(self.cargo_proof_inventory.as_ref());
        if has_gate_failing_cargo_exclusions
            && (self.success
                || gate_success
                || !matches!(
                    summary.verdict,
                    trust_types::CrateVerdict::HasViolations
                        | trust_types::CrateVerdict::Inconclusive
                ))
        {
            return false;
        }
        gate_success == self.success
    }

    fn complete_authorized_rows(&self) -> Option<AuthorizedRows<'_>> {
        let serialized = self.serialized_publication_state()?;
        self.live_transport_authority.as_ref()?.validate_complete_report(
            &self.report_subject,
            &self.results,
            &self.zero_obligation_functions,
            &serialized,
            self.proof_artifact_root.as_deref(),
        )
    }

    pub(crate) fn render(&self, format: OutputFormat, report_dir: Option<&str>) -> io::Result<()> {
        self.render_with_unsafe_memory_report(format, report_dir, None)
    }

    pub(crate) fn render_with_unsafe_memory_report(
        &self,
        format: OutputFormat,
        report_dir: Option<&str>,
        unsafe_memory: Option<&UnsafeMemoryReportRequest>,
    ) -> io::Result<()> {
        if self.complete_authorized_rows().is_none() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "canonical Targo output requires a valid final publication seal over rows, coverage, policy, gate, and exit state",
            ));
        }
        let unsafe_memory_preflight = if let Some(request) = unsafe_memory {
            if report_dir.is_none() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "unsafe-memory proof wrapper emission requires a report directory",
                ));
            }
            Some(preflight_unsafe_memory_report(request, self)?)
        } else {
            None
        };

        // Reuse the exact bounded bytes/DTO retained at seal time. Rebuilding
        // would inject a fresh wall-clock timestamp and elapsed duration, and
        // repeated full serialization needlessly multiplied peak memory.
        let (sealed_report, serialized_canonical) = self
            .live_transport_authority
            .as_ref()
            .and_then(LiveTransportAuthority::sealed_canonical_publication)
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    "canonical report no longer matches its final publication seal",
                )
            })?;
        let trust_report = sealed_report.clone();
        if report_contains_path_materializations(&trust_report) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "sealed canonical report retained mutable path-backed proof evidence",
            ));
        }
        let html_report = (matches!(format, OutputFormat::Html) || report_dir.is_some())
            .then(|| trust_report::html_report::generate_html_report(&trust_report));

        // Persist requested evidence before printing machine-readable stdout so
        // consumers cannot observe a success-shaped report from a failed
        // artifact gate.
        if let Some(dir) = report_dir {
            let output_dir = Path::new(dir);
            write_report_artifacts_from_root(
                &trust_report,
                output_dir,
                html_report
                    .as_deref()
                    .expect("HTML report should be rendered when writing report artifacts"),
                self.proof_artifact_root.as_deref(),
                unsafe_memory_preflight,
                Some(serialized_canonical),
            )?;
        }

        match format {
            OutputFormat::Terminal => {
                self.render_terminal();
                // Also print the trust-report text summary for richer output.
                eprintln!();
                eprintln!("{}", trust_report::format_json_summary(&trust_report));
            }
            OutputFormat::Json => {
                // Emit the exact compact bytes covered by the canonical seal.
                let stdout = io::stdout();
                let mut stdout = stdout.lock();
                stdout.write_all(serialized_canonical)?;
                stdout.write_all(b"\n")?;
                stdout.flush()?;
            }
            OutputFormat::Html => {
                // Use trust-report HTML generator with dashboard.
                println!(
                    "{}",
                    html_report
                        .as_deref()
                        .expect("HTML output should be rendered when format=html")
                );
            }
        }

        Ok(())
    }

    fn render_terminal(&self) {
        for line in self.terminal_lines() {
            eprintln!("{line}");
        }
    }

    fn terminal_lines(&self) -> Vec<String> {
        let mut lines = Vec::with_capacity(self.results.len() + 8);
        lines.push(String::new());
        lines.push("=== Trust Verification Report ===".to_string());
        lines.push(format!(
            "Level: {} | Solver timeout: {}ms | Function budget: {}ms | Duration: {}ms",
            self.config.level,
            self.config.timeout_ms,
            self.config.function_budget_ms,
            self.duration_ms
        ));
        lines.push(String::new());

        if self.results.is_empty() {
            lines.push("  No verification obligations found.".to_string());
        } else {
            lines.extend(self.results.iter().map(terminal_result_line));
        }

        let full_verifier_lines =
            full_verifier_terminal_lines(&self.results, &self.compiler_diagnostics);
        if !full_verifier_lines.is_empty() {
            lines.push(String::new());
            lines.extend(full_verifier_lines);
        }

        lines.push(String::new());
        lines.push(format!(
            "Summary: {} proved, {} failed, {} runtime-checked, {} assumed, {} mandated, {} contract-panic, {} inconclusive ({} total)",
            self.proved,
            self.failed,
            self.runtime_checked,
            self.assumed,
            self.mandated,
            self.contract_panics,
            self.unknown,
            self.total
        ));
        // Trust (verify-cache): informational cache-replay line. These obligations
        // were proved earlier on byte-identical inputs (sound-key hit) and skipped
        // this run; they are still counted conservatively above (no proof credit),
        // so this is purely a re-verification-saved signal.
        if self.cached > 0 {
            let pct =
                if self.total > 0 { (self.cached as f64 / self.total as f64) * 100.0 } else { 0.0 };
            lines.push(format!(
                "Cache: {} of {} obligation(s) replayed from verification cache ({:.0}% hit rate)",
                self.cached, self.total, pct
            ));
        }
        // Trust (assertion-grade coverage): the whole-crate coverage line. A
        // shortfall is a FAIL-CLOSED condition (the gate was capped at
        // INCONCLUSIVE by `apply_coverage_gate`), so say so loudly; an absent
        // row (older compiler) is honestly UNKNOWN, never silently complete.
        lines.push(self.coverage_line());
        if let Some(test_execution) = self.test_execution.as_ref() {
            lines.push(certified_test_execution_terminal_line(test_execution));
        }
        let active_exclusions = cargo_active_exclusion_labels(self.cargo_proof_inventory.as_ref());
        if !active_exclusions.is_empty() {
            lines.push(format!(
                "Cargo proof scope: INCOMPLETE — {} active Unit(s) excluded from the authenticated proof frontier",
                active_exclusions.len(),
            ));
            lines.extend(
                active_exclusions
                    .into_iter()
                    .map(|identity| format!("  Excluded Cargo Unit: {identity}")),
            );
        }
        lines.push(format!("Result: {}", self.terminal_status_label()));
        lines.push("=================================".to_string());
        lines
    }

    /// Trust (assertion-grade coverage): the human report's coverage line.
    fn coverage_line(&self) -> String {
        match &self.coverage {
            Some(cov) if cov.coverage_complete => format!(
                "Coverage: {}/{} eligible function bodies verified (complete)",
                cov.processed, cov.eligible
            ),
            Some(cov) => format!(
                "Coverage: {}/{} — coverage shortfall: {} function(s) were never verified \
                 (fail-closed: never a passing gate)",
                cov.processed,
                cov.eligible,
                cov.eligible.saturating_sub(cov.processed)
            ),
            None => "Coverage: unknown (compiler emitted no coverage_summary transport row; \
                     older toolchain?)"
                .to_string(),
        }
    }

    fn terminal_status_label(&self) -> String {
        // The final gate records setup/evidence failures as well as solver
        // outcomes.  Prefer it whenever present so an exit-2 transport failure
        // cannot be mislabeled merely `INCONCLUSIVE` because rustc itself
        // happened to exit zero.
        if let Some(gate) = &self.gate {
            return match gate.decision.as_str() {
                "pass" if gate.exit_code == 0 => "PASS".to_string(),
                "conditional-pass" if gate.exit_code == 0 => format!(
                    "PASS (conditional: {} assumption{}, {} design mandate{}, {} runtime-checked, {} contract-panic{}; see Assumptions ledger)",
                    gate.counts.assumed,
                    plural_s(gate.counts.assumed),
                    gate.counts.mandated,
                    plural_s(gate.counts.mandated),
                    gate.counts.runtime_checked,
                    gate.counts.contract_panics,
                    plural_s(gate.counts.contract_panics),
                ),
                "fail" => "FAIL".to_string(),
                "inconclusive" => "INCONCLUSIVE".to_string(),
                _ => "FAIL".to_string(),
            };
        }
        if self.hardened_proof_gate_failure().is_some() {
            return "FAIL".to_string();
        }
        if !self.success {
            // A refutation (or a nonzero compiler exit) is a hard FAIL; every
            // other non-success state (genuine unknown, no obligations) is
            // INCONCLUSIVE — honest, since nothing was refuted.
            return if self.failed > 0 || self.exit_code != 0 {
                "FAIL".to_string()
            } else {
                "INCONCLUSIVE".to_string()
            };
        }
        // Success. A pass resting on ANY explicit ledger row (assumption /
        // design mandate / runtime-checked) is a CONDITIONAL pass and must say
        // so — the label names the counts the exit-0 is conditional on. Only an
        // all-proved run earns a bare PASS. (dep-TCB entries never appear here:
        // they are structural and always present, so they never demote the
        // label — see the always-printed dep-TCB ledger block instead.)
        let conditional =
            self.assumed + self.mandated + self.runtime_checked + self.contract_panics;
        if conditional > 0 {
            format!(
                "PASS (conditional: {} assumption{}, {} design mandate{}, {} runtime-checked, {} contract-panic{}; see Assumptions ledger)",
                self.assumed,
                plural_s(self.assumed),
                self.mandated,
                plural_s(self.mandated),
                self.runtime_checked,
                self.contract_panics,
                plural_s(self.contract_panics),
            )
        } else {
            "PASS".to_string()
        }
    }

    pub(crate) fn hardened_proof_gate_failure(&self) -> Option<HardenedProofGateFailure> {
        if !self.config.hardened {
            return None;
        }

        let context = build_hardened_report_context(
            &self.results,
            &self.compiler_diagnostics,
            &self.config,
            self.proof_artifact_root.as_deref(),
            self.live_transport_authority.as_ref(),
            &self.report_subject,
        )?;
        let summary = context.summary?;
        if summary.hardened_obligations == 0
            || summary.proof_evidence_entries == summary.hardened_obligations
        {
            return None;
        }

        Some(HardenedProofGateFailure {
            hardened_obligations: summary.hardened_obligations,
            proof_evidence_entries: summary.proof_evidence_entries,
        })
    }

    /// Convert targo-trust parsed results to trust-types pairs and build a
    /// `JsonProofReport` via trust-report.
    ///
    /// This bridges the gap between the lightweight text-parsed
    /// results in targo-trust and the canonical trust-report JSON format.
    fn to_trust_report(&self) -> trust_types::JsonProofReport {
        let live_authority = self.complete_authorized_rows();
        if live_authority.is_some() {
            if let Some((sealed, _)) = self
                .live_transport_authority
                .as_ref()
                .and_then(LiveTransportAuthority::sealed_canonical_publication)
            {
                return sealed.clone();
            }
        }
        let complete_report_authority =
            live_authority.as_ref().and(self.live_transport_authority.as_ref());
        let pairs: Vec<(TrustVc, TrustVr)> = self
            .results
            .iter()
            .enumerate()
            .map(|(index, r)| {
                let compiler_design_mandate = live_authority.as_ref().is_some_and(|authority| {
                    authority.authorizes_row(index, r) && transport_design_mandate(r)
                });
                // A compiler-authorized DESIGN MANDATE must classify canonically
                // as a design requirement, which trust-report labels ONLY on a
                // `HardenedBoundary` kind with a `Bool(true)` formula.
                // `report_vc_kind` maps an unrecognized full-verifier kind to
                // `Assertion` before its hardened-category branch, so a mandate
                // row surfaced through the full-verifier lane (e.g. `_print`
                // process semantics) would silently lose its mandate label —
                // miscounted as a genuine unknown and diverging from the internal
                // outcome partition (which trusts the same authorized bit).
                // Prefer the hardened mapping for authorized mandates; everything
                // else keeps the ordinary mapping.
                let mandate_category =
                    if compiler_design_mandate { parse_hardened_category(&r.kind) } else { None };
                let kind = match mandate_category {
                    Some(category) => VcKind::HardenedBoundary {
                        category,
                        callee: if r.function.is_empty() {
                            r.kind.clone()
                        } else {
                            r.function.clone()
                        },
                        detail: if r.message.trim().is_empty() {
                            format!("hardened verification category {}", category.as_tag())
                        } else {
                            r.message.clone()
                        },
                    },
                    None => report_vc_kind(r),
                };
                let vc = TrustVc {
                    kind,
                    function: if r.function.is_empty() {
                        r.kind.clone().into()
                    } else {
                        r.function.clone().into()
                    },
                    location: r.location.clone().unwrap_or_else(SourceSpan::default),
                    // targo does not have the real VC formula; this field is a
                    // placeholder EXCEPT for its one classification effect:
                    // trust-report labels a `HardenedBoundary` row with a
                    // `Bool(true)` formula as a design_requirement. That label
                    // must follow the COMPILER's design-mandate bit on the
                    // transport row — fabricating `Bool(true)` for every row
                    // (as this used to) mislabeled genuinely PROVED hardened
                    // obligations (e.g. `[unsafe:sep]` VCs) as design
                    // requirements. Non-mandate rows carry the fail-closed
                    // `Bool(false)` placeholder, which classifies nothing.
                    formula: if compiler_design_mandate {
                        Formula::Bool(true)
                    } else {
                        Formula::Bool(false)
                    },
                    contract_metadata: None,
                    // Not a contract-derived VC: no obligation to back-reference.
                    obligation: None,
                };
                // Contract-panic rows carry no proof and are neither ordinary
                // refutations nor runtime evidence. Keep the canonical report
                // summary aligned with the gate's disjoint partition by
                // representing every declared row (including a malformed row
                // that claimed proof) as fail-closed Unknown.
                let contract_panic = is_declared_contract_panic_result(r);
                let vr = if contract_panic {
                    TrustVr::Unknown {
                        solver: r.backend.clone().into(),
                        time_ms: r.time_ms.unwrap_or(0),
                        reason: "declared contract panic (conditional policy row; no proof credit)"
                            .to_string(),
                    }
                } else {
                    match r.outcome {
                        VerificationOutcome::Proved => TrustVr::Proved {
                            solver: r.backend.clone().into(),
                            time_ms: r.time_ms.unwrap_or(0),
                            strength: ProofStrength::smt_unsat(),
                            proof_certificate: None,
                            solver_warnings: None,
                            native_proof_envelope: None,
                        },
                        VerificationOutcome::Failed => TrustVr::Failed {
                            solver: r.backend.clone().into(),
                            time_ms: r.time_ms.unwrap_or(0),
                            counterexample: r.counterexample.clone(),
                        },
                        VerificationOutcome::RuntimeChecked | VerificationOutcome::Unknown => {
                            TrustVr::Unknown {
                                solver: r.backend.clone().into(),
                                time_ms: r.time_ms.unwrap_or(0),
                                reason: r.reason.clone().unwrap_or_else(|| {
                                    "unproved obligation with runtime check".to_string()
                                }),
                            }
                        }
                        VerificationOutcome::Timeout => TrustVr::Timeout {
                            solver: r.backend.clone().into(),
                            timeout_ms: r.time_ms.unwrap_or(0),
                        },
                    }
                };
                (vc, vr)
            })
            .collect();
        let full_verifier_diagnostics =
            native_full_verifier_diagnostics(&self.compiler_diagnostics);
        // Compiler transport already carries an explicit normalized outcome.
        // Never re-infer RuntimeChecked from a VC kind or from a guessed
        // overflow-check policy: that used to turn authenticated Unknown rows
        // into canonical runtime-checked rows.  Build statically, then restore
        // only the compiler's explicit RuntimeChecked labels below while the
        // exact live row receipt still validates.
        let policy = RuntimeCheckPolicy::ForceStatic;
        // Public status/evidence DTOs are never proof authority. Start through
        // trust-report's fail-closed raw adapter (every caller-supplied Proved
        // label becomes Unknown), then restore proof credit only while this
        // exact result vector still matches a private receipt minted from the
        // authenticated live compiler channel.
        let mut report = trust_report::build_json_report_with_policy(
            &self.report_subject,
            &pairs,
            policy,
            false,
        );
        // Keep the compiler's exact adjacent description. New transport also
        // carries the lossless typed `VcKind`; legacy fieldless tags are
        // decoded conservatively below. Neither field grants proof authority.
        restore_typed_transport_descriptions(&mut report, &self.results);
        if live_authority.is_some() {
            report.functions.extend(
                self.zero_obligation_functions.iter().cloned().map(zero_obligation_function_report),
            );
            report.functions.sort_by(|left, right| left.function.cmp(&right.function));
        }
        self.attach_live_transport_evidence(
            &mut report,
            &full_verifier_diagnostics,
            live_authority.as_ref(),
        );
        append_full_verifier_unknown_diagnostics(
            &mut report,
            &self.results,
            &full_verifier_diagnostics,
        );
        // Preserve the canonical project policy in every persisted/JSON report.
        // Both policy fields are optional so reports produced by older Trust
        // versions and non-Targo frontends remain deserializable, while Targo
        // reports always carry the exact configured limits for safe diffing.
        report.metadata.timeout_ms = Some(self.config.timeout_ms);
        report.metadata.function_budget_ms = Some(self.config.function_budget_ms);
        report.summary.proof_grade_engine_statuses =
            trust_types::summarize_proof_grade_engine_statuses(&report.functions);
        attach_hardened_report_context(
            &mut report,
            &self.results,
            &self.compiler_diagnostics,
            &self.config,
            self.proof_artifact_root.as_deref(),
            complete_report_authority,
            &self.report_subject,
        );
        // Trust (assumption ledger): everything this report's verdict is
        // conditional on — crate-scope dep-TCB entries plus function-scope
        // capability gaps. Reads the RAW transport `kind` (before
        // `report_vc_kind` folds it) so tags survive verbatim. The rows also
        // remain Unknown obligations above, so the verdict stays
        // Inconclusive/fail-closed; entries here are never proof inputs.
        report.assumptions = self
            .dep_assumptions
            .iter()
            .cloned()
            .chain(self.results.iter().filter_map(assumption_entry_from_result))
            .collect();
        // Trust (fail-closed labeling): a nonzero build/compile exit or an
        // active Cargo Unit outside the authenticated proof frontier that is NOT
        // admitted to the dependency-TCB ledger means the crate did NOT verify.
        // Rows proved inside the smaller frontier cannot lift the whole crate to
        // `Verified`. Cap the crate verdict: `HasViolations` if any obligation
        // refuted, else `Inconclusive`. dep-TCB-admitted exclusions are recorded
        // `Conditional` assumptions (trusted-assumed, never proved) and so do
        // not by themselves cap the verdict.
        if !self.success
            || self.exit_code != 0
            || cargo_has_gate_failing_exclusions(self.cargo_proof_inventory.as_ref())
        {
            report.summary.verdict = if self.failed > 0 {
                trust_types::CrateVerdict::HasViolations
            } else {
                trust_types::CrateVerdict::Inconclusive
            };
        }
        // Trust (green front door, Stage 2): mirror the tiered exit-code gate
        // decision into the report. This is SEPARATE from the verdict lattice
        // above — the verdict stays fail-closed, while this records why the
        // shell exited as it did.
        report.verification_gate = self.gate.clone();
        report.cargo_proof_inventory = self.cargo_proof_inventory.clone();
        report
    }

    fn attach_live_transport_evidence(
        &self,
        report: &mut trust_types::JsonProofReport,
        full_verifier_diagnostics: &[String],
        authority: Option<&AuthorizedRows<'_>>,
    ) {
        let Some(authority) = authority else {
            return;
        };

        let function_indices = report
            .functions
            .iter()
            .enumerate()
            .map(|(index, function)| (function.function.clone(), index))
            .collect::<BTreeMap<_, _>>();
        let mut cursors = vec![0usize; report.functions.len()];
        let mut attachments = Vec::with_capacity(self.results.len());

        // Resolve every target before changing any report row. This keeps the
        // result/evidence pairing atomic: a grouping/cardinality mismatch makes
        // the whole attachment step fail closed instead of partially promoting
        // an index-shifted prefix.
        for (result_index, result) in self.results.iter().enumerate() {
            let function_name = report_function_name(result);
            let Some(function_index) = function_indices.get(&function_name).copied() else {
                return;
            };
            let obligation_index = cursors[function_index];
            if obligation_index >= report.functions[function_index].obligations.len() {
                return;
            }
            cursors[function_index] += 1;

            let structured = structured_transport_evidence(result);
            let transport_evidence = structured.as_ref().and_then(native_transport_evidence);
            let proof_evidence = authority
                .authorizes_proved_row(result_index, result)
                .then(|| {
                    let diagnostics = if is_full_verifier_result(result) {
                        full_verifier_diagnostics
                    } else {
                        &[]
                    };
                    native_proof_evidence_report(
                        result,
                        structured.as_ref(),
                        diagnostics,
                        self.proof_artifact_root.as_deref(),
                    )
                    .or_else(|| kernel_proof_evidence_report(result, structured.as_ref()))
                })
                .flatten();
            let unsupported_favorable =
                matches!(
                    result.outcome,
                    VerificationOutcome::Proved | VerificationOutcome::RuntimeChecked
                ) && matches!(report_vc_kind(result), VcKind::UnsupportedMir { .. });
            let outcome =
                if unsupported_favorable { VerificationOutcome::Unknown } else { result.outcome };
            let reason = if unsupported_favorable {
                Some(
                    "unsupported MIR classification cannot carry proof or runtime-check authority"
                        .to_string(),
                )
            } else {
                result.reason.clone()
            };
            attachments.push((
                function_index,
                obligation_index,
                outcome,
                result.time_ms.unwrap_or(0),
                reason,
                structured.and_then(|evidence| evidence.obligation_id),
                transport_evidence,
                proof_evidence,
            ));
        }
        if cursors
            .iter()
            .enumerate()
            .any(|(index, cursor)| *cursor != report.functions[index].obligations.len())
        {
            return;
        }

        for (
            function_index,
            obligation_index,
            outcome,
            time_ms,
            reason,
            obligation_id,
            transport,
            proof,
        ) in attachments
        {
            let obligation = &mut report.functions[function_index].obligations[obligation_index];
            obligation.obligation_id = obligation_id;
            obligation.transport_evidence = transport;
            match (outcome, proof) {
                (VerificationOutcome::Proved, Some(proof)) => {
                    obligation.outcome =
                        ObligationOutcome::Proved { strength: proof.strength.clone() };
                    obligation.evidence = Some(proof.evidence.clone());
                    obligation.proof_evidence = Some(proof);
                }
                (VerificationOutcome::RuntimeChecked, _) => {
                    obligation.outcome = ObligationOutcome::RuntimeChecked { note: reason };
                    obligation.evidence = None;
                    obligation.proof_evidence = None;
                }
                (VerificationOutcome::Timeout, _) => {
                    obligation.outcome = ObligationOutcome::Timeout { timeout_ms: time_ms };
                    obligation.evidence = None;
                    obligation.proof_evidence = None;
                }
                _ => {}
            }
        }
        report.recompute_summaries_from_obligation_outcomes();
    }
}

fn zero_obligation_function_report(function: String) -> FunctionProofReport {
    FunctionProofReport {
        function,
        summary: FunctionSummary {
            total_obligations: 0,
            proved: 0,
            runtime_checked: 0,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            design_requirements: 0,
            unattributed_failed: 0,
            unattributed_unknown: 0,
            unattributed_proved: 0,
            total_time_ms: 0,
            max_proof_level: None,
            verdict: FunctionVerdict::NoObligations,
        },
        obligations: Vec::new(),
    }
}

/// Stable, single-line terminal form of the typed two-phase Cargo test state.
/// Keep the field names machine-greppable while leaving canonical structured
/// consumption to report.json. Optional fields appear only after that phase of
/// the protocol has produced them.
fn certified_test_execution_terminal_line(execution: &CertifiedTestExecutionReport) -> String {
    let state = match execution.phase_b_state {
        CertifiedTestExecutionPhaseState::NotRequested => "not-requested",
        CertifiedTestExecutionPhaseState::Blocked => "blocked",
        CertifiedTestExecutionPhaseState::Started => "started",
        CertifiedTestExecutionPhaseState::CargoInvocationExited => "cargo-invocation-exited",
    };
    let completion_scope = match execution.completion_scope {
        CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1 => {
            "top-level-cargo-child-exit-only-v1"
        }
    };
    let mut fields = vec![
        format!("schema={}", execution.schema),
        format!("completion_scope={completion_scope}"),
        format!("state={state}"),
        format!("requested={}", execution.requested),
        format!("compile_only={}", execution.compile_only),
        format!("phase_a_exit={}", execution.phase_a_status),
        format!("phase_a_success={}", execution.phase_a_success),
    ];
    if execution.authorized_inventory_sha256.is_some()
        || !execution.authorized_executables.is_empty()
    {
        fields.push(format!("authorized_executables={}", execution.authorized_executables.len()));
    }
    if let Some(exit) = execution.phase_b_exit {
        fields.push(format!("phase_b_exit={exit}"));
    }
    if let Some(blocker) = execution.blocker.as_deref() {
        // Debug string formatting quotes and escapes embedded newlines/control
        // bytes, preserving the durable one-record-per-line terminal contract.
        fields.push(format!("blocker={blocker:?}"));
    }
    format!("Certified test execution: {}", fields.join(" "))
}

/// Trust (assumption ledger): map an `assumption:<tag>` transport row to its
/// function-scope ledger entry.
fn assumption_entry_from_result(
    result: &VerificationResult,
) -> Option<trust_types::AssumptionEntry> {
    let tag = result.kind.strip_prefix("assumption:")?;
    Some(trust_types::AssumptionEntry {
        scope: "function".to_string(),
        subject: result.function.clone(),
        tag: tag.to_string(),
        detail: result.message.clone(),
        location: result.location.clone(),
        source: result.backend.clone(),
    })
}

fn report_vc_kind(result: &VerificationResult) -> VcKind {
    if is_declared_contract_panic_result(result) {
        // A declared contract panic is an explicit policy ledger row, not a
        // Rust runtime-check fallback. `UnsupportedMir` is the canonical
        // no-fallback carrier, so RuntimeCheckPolicy::Auto cannot silently
        // relabel this no-proof row as RuntimeChecked.
        return VcKind::UnsupportedMir {
            kind: result.kind.clone(),
            detail: result.message.clone(),
        };
    }
    if result.kind.starts_with("assumption:") {
        // Policy reclassification owns this row even if a malformed/legacy
        // producer retained an earlier typed payload. Never resurrect the
        // original VC beneath an explicit unverified-assumption tag.
        return VcKind::UnsupportedMir {
            kind: result.kind.clone(),
            detail: result.message.clone(),
        };
    }
    match exact_transport_vc_kind(result) {
        Ok(Some(typed_kind)) => {
            // The exact typed payload preserves fields that the compact tag
            // drops: operand types, temporal machines, and deep-property
            // parameters. It is report classification only; live private row
            // authority still gates every proof outcome/evidence attachment.
            return typed_kind;
        }
        Err(()) => {
            // A split-brain payload must not select whichever half is more
            // favorable. The shared tag function and exact description bind
            // the rich DTO to both adjacent legacy fields.
            return VcKind::UnsupportedMir {
                kind: result.kind.clone(),
                detail: "typed VC kind disagrees with its compact tag or description".to_string(),
            };
        }
        Ok(None) => {}
    }
    if let Some(category) = parse_hardened_category(&result.kind) {
        return VcKind::HardenedBoundary {
            category,
            callee: if result.function.is_empty() {
                result.kind.clone()
            } else {
                result.function.clone()
            },
            detail: if result.message.trim().is_empty() {
                format!("hardened verification category {}", category.as_tag())
            } else {
                result.message.clone()
            },
        };
    }
    if let Some(kind) = parse_exact_legacy_vc_kind(&result.kind, &result.message) {
        return kind;
    }
    if is_full_verifier_result(result)
        || crate::types::compact_vc_tag_requires_typed_kind(&result.kind)
    {
        // A missing typed payload cannot be repaired by inventing fields. In
        // particular, Assertion would falsely claim a runtime fallback for
        // temporal/deep obligations. UnsupportedMir is the no-proof,
        // no-runtime-fallback carrier for legacy loss.
        return VcKind::UnsupportedMir {
            kind: result.kind.clone(),
            detail: result.message.clone(),
        };
    }
    VcKind::Assertion { message: result.kind.clone() }
}

fn exact_transport_vc_kind(result: &VerificationResult) -> Result<Option<VcKind>, ()> {
    crate::types::exact_structured_transport_vc_kind(result)
}

/// Restore the exact compiler description after the compact transport tag has
/// been expanded to a report classification.
///
/// This update is deliberately atomic.  `trust-report` groups rows by function;
/// if that grouping ever stops being a one-to-one projection of `results`, no
/// descriptions are changed.  Proof outcomes/evidence are untouched.
fn restore_typed_transport_descriptions(
    report: &mut trust_types::JsonProofReport,
    results: &[VerificationResult],
) {
    let function_indices = report
        .functions
        .iter()
        .enumerate()
        .map(|(index, function)| (function.function.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut cursors = vec![0usize; report.functions.len()];
    let mut replacements = Vec::new();

    for result in results {
        let function_name = report_function_name(result);
        let Some(function_index) = function_indices.get(&function_name).copied() else {
            return;
        };
        let obligation_index = cursors[function_index];
        if obligation_index >= report.functions[function_index].obligations.len() {
            return;
        }
        cursors[function_index] += 1;

        if !result.message.trim().is_empty()
            && (exact_transport_vc_kind(result).is_ok_and(|kind| kind.is_some())
                || parse_exact_legacy_vc_kind(&result.kind, &result.message).is_some())
        {
            replacements.push((function_index, obligation_index, result.message.clone()));
        }
    }

    if cursors
        .iter()
        .enumerate()
        .any(|(index, cursor)| *cursor != report.functions[index].obligations.len())
    {
        return;
    }

    for (function_index, obligation_index, description) in replacements {
        report.functions[function_index].obligations[obligation_index].description = description;
    }
}

fn is_declared_contract_panic_result(result: &VerificationResult) -> bool {
    trust_types::tolerance::classify_contract_panic(&trust_types::tolerance::ContractPanicView {
        text: &result.message,
        row_kind: Some(&result.kind),
    })
    .is_declared()
}

fn append_full_verifier_unknown_diagnostics(
    report: &mut trust_types::JsonProofReport,
    results: &[VerificationResult],
    run_diagnostics: &[String],
) {
    let mut by_function: BTreeMap<String, VecDeque<&VerificationResult>> = BTreeMap::new();
    for result in results {
        by_function.entry(report_function_name(result)).or_default().push_back(result);
    }

    for function in &mut report.functions {
        let Some(function_results) = by_function.get_mut(&function.function) else {
            continue;
        };
        for obligation in &mut function.obligations {
            let Some(result) = function_results.pop_front() else {
                break;
            };
            if !is_full_verifier_result(result) {
                continue;
            }
            if let ObligationOutcome::Unknown { reason } = &mut obligation.outcome {
                append_full_verifier_diagnostics_to_reason(reason, run_diagnostics);
            }
        }
    }
}

fn attach_hardened_report_context(
    report: &mut trust_types::JsonProofReport,
    results: &[VerificationResult],
    diagnostics: &[CompilerDiagnostic],
    config: &ReportConfig,
    materialization_root: Option<&Path>,
    authority: Option<&LiveTransportAuthority>,
    report_subject: &str,
) {
    report.hardened = build_hardened_report_context(
        results,
        diagnostics,
        config,
        materialization_root,
        authority,
        report_subject,
    );
}

fn build_hardened_report_context(
    results: &[VerificationResult],
    diagnostics: &[CompilerDiagnostic],
    config: &ReportConfig,
    materialization_root: Option<&Path>,
    authority: Option<&LiveTransportAuthority>,
    report_subject: &str,
) -> Option<HardenedReportContext> {
    let authorized_rows =
        authority.and_then(|authority| authority.validate_rows(report_subject, results));
    let mut observed_categories = BTreeSet::new();
    let mut boundary_inventory = Vec::new();
    let mut hardened_obligations = 0;

    // Dedup hardened boundaries by exact compiler claim identity. The SAME VC
    // can yield more than one
    // VerificationResult — e.g. a shift panic boundary discharged BOTH by the
    // native trust-mc CHC lane (which carries publishable native trust_ir
    // evidence) AND, redundantly, by the ay Farkas → clean-CIC lane (a second
    // result for the identical assert, carrying a kernel-checked clean-CIC term
    // but NO native trust_ir). Counting each result as its own obligation
    // double-counts that one boundary and then demands publishable NATIVE
    // evidence from the clean-CIC twin, which by construction has none — a
    // spurious gate miss (observed: a3d-kernel `octree_node_count`'s
    // `1u64 << exp`). Keep ONE representative per boundary, preferring a result
    // that carries publishable proof — either a strict native envelope or a
    // content-addressed clean-CIC kernel proof.
    //
    // SOUNDNESS: source/display identity is not logical identity. Macro-expanded
    // checks can share function, kind, message, and span, and delimiter-joined
    // strings are not an injective tuple encoding. Only rows authorized by the
    // live compiler vector and carrying the same exact canonical claim digest
    // may share a representative. Rows without that identity are unique by
    // index and therefore fail closed rather than donating a sibling's proof.
    let mut representative: std::collections::BTreeMap<HardenedBoundaryIdentity, usize> =
        std::collections::BTreeMap::new();
    for (index, result) in results.iter().enumerate() {
        if parse_hardened_category(&result.kind).is_none() {
            continue;
        }
        let key = hardened_boundary_identity(authorized_rows.as_ref(), index, result);
        let publishable = authorized_rows.as_ref().is_some_and(|authority| {
            authority.authorizes_proved_row(index, result)
                && publishable_hardened_proof(
                    result,
                    structured_transport_evidence(result).as_ref(),
                    materialization_root,
                )
                .is_some()
        });
        match representative.get(&key).copied() {
            None => {
                representative.insert(key, index);
            }
            Some(existing) if publishable => {
                let existing_publishable = authorized_rows.as_ref().is_some_and(|authority| {
                    authority.authorizes_proved_row(existing, &results[existing])
                        && publishable_hardened_proof(
                            &results[existing],
                            structured_transport_evidence(&results[existing]).as_ref(),
                            materialization_root,
                        )
                        .is_some()
                });
                if !existing_publishable {
                    representative.insert(key, index);
                }
            }
            Some(_) => {}
        }
    }
    let chosen: std::collections::BTreeSet<usize> = representative.values().copied().collect();

    for (index, result) in results.iter().enumerate() {
        let Some(category) = parse_hardened_category(&result.kind) else {
            continue;
        };
        // Skip redundant duplicates of a boundary already represented above.
        if !chosen.contains(&index) {
            continue;
        }

        // The hardened proof-evidence denominator counts ONLY proved,
        // non-mandate hardened rows. Two exclusions:
        //
        //   * DESIGN MANDATE rows (hardened-category VC with a tautology `true`
        //     violation formula — e.g. "[unsafe] missing SAFETY comment") can
        //     never carry proof evidence BY CONSTRUCTION. The bit is the
        //     structured transport bit the COMPILER set (it alone sees the VC
        //     formula); targo never guesses it from row text.
        //   * NON-PROVED hardened rows (Unknown/Timeout/Failed). The numerator
        //     (`proof_evidence_entries`) is only ever minted from rows with
        //     `outcome.is_proved()` (`structured_native_proof_is_publishable`),
        //     so an unknown hardened row could only ever make the gate FAIL —
        //     mislabeling a run in which nothing was refuted as FAIL. Excluding
        //     it makes the terminal label INCONCLUSIVE instead (more honest);
        //     no run that passes today can start failing, because the numerator
        //     ⊆ the new denominator ⊆ the old denominator (green front door E4).
        //
        // Excluded rows still appear in the boundary INVENTORY below — never
        // hidden.
        let structured = authorized_rows
            .as_ref()
            .filter(|authority| authority.authorizes_row(index, result))
            .and_then(|_| structured_transport_evidence(result));
        let design_mandate = structured.as_ref().is_some_and(|evidence| evidence.design_mandate);
        if !design_mandate && result.outcome.is_proved() {
            hardened_obligations += 1;
        }

        let category = category.as_tag().to_string();
        observed_categories.insert(category.clone());

        let obligation_id = structured.as_ref().and_then(|evidence| evidence.obligation_id.clone());
        let boundary = hardened_boundary_item(result, &category);

        boundary_inventory.push(hardened_inventory_entry(
            result,
            &category,
            &boundary,
            obligation_id.clone(),
        ));

        boundary_inventory.extend(hardened_model_assumption_entries(
            index,
            result,
            &category,
            &boundary,
            obligation_id.clone(),
            structured.as_ref(),
        ));

        // A design mandate is not in the denominator, so it must not mint a
        // ProofEvidence numerator entry either (it cannot have one anyway —
        // see above — but keep the roles structurally paired). Non-proved
        // hardened rows are likewise no longer in the denominator (E4), and
        // cannot mint a numerator entry (`publishable_native_proof_components`
        // requires `outcome.is_proved()`), so the numerator ⊆ denominator
        // invariant holds.
        if design_mandate {
            continue;
        }

        if let Some(proof) = authorized_rows
            .as_ref()
            .filter(|authority| authority.authorizes_proved_row(index, result))
            .and_then(|_| {
                // A NATIVE (trust-mc/ay) proof carries a native TrustIR envelope.
                // A clean CIC KERNEL proof (`certify_vc` — e.g. a `(a/c)+(b/c)`
                // no-overflow refutation) carries none, since it is a zero-trust
                // kernel refutation, not a native solver run — but it is the
                // STRONGEST evidence a hardened boundary can carry, so accept it
                // too (gated by the same strict `clean_cic_transport_proof_is_publishable`
                // contract the general report path uses via `kernel_proof_evidence_report`).
                publishable_hardened_proof(result, structured.as_ref(), materialization_root)
            })
        {
            if let Some(entry) =
                hardened_proof_evidence_entry(result, &category, &boundary, obligation_id, proof)
            {
                boundary_inventory.push(entry);
            }
        }
    }

    let profile_name = config
        .trust_profile
        .clone()
        .or_else(|| detected_hardened_profile_name(diagnostics))
        .or_else(|| config.hardened.then(|| DEFAULT_HARDENED_PROFILE.to_string()));

    if hardened_obligations == 0 && profile_name.is_none() {
        return None;
    }

    let inventory_entries = boundary_inventory
        .iter()
        .filter(|entry| matches!(entry.role, HardenedBoundaryInventoryRole::Inventory))
        .count();
    let model_assumptions = boundary_inventory
        .iter()
        .filter(|entry| matches!(entry.role, HardenedBoundaryInventoryRole::ModelAssumption))
        .count();
    let proof_evidence_entries = boundary_inventory
        .iter()
        .filter(|entry| matches!(entry.role, HardenedBoundaryInventoryRole::ProofEvidence))
        .count();
    let proved_hardened_obligations = proof_evidence_entries;
    Some(HardenedReportContext {
        profile: Some(HardenedProfileReport {
            name: profile_name.clone(),
            version: None,
            enabled_categories: hardened_profile_enabled_categories(
                profile_name.as_deref(),
                &observed_categories,
            ),
        }),
        assurance: Some(HardenedAssuranceReport {
            level: Some(hardened_assurance_level(hardened_obligations, proof_evidence_entries)),
            model: (model_assumptions > 0).then(|| "reported_hardened_model".to_string()),
            proof_evidence_policy: Some(
                "native hardened checks fail unless every hardened obligation has publishable structured native proof evidence"
                    .to_string(),
            ),
            proof_evidence_required: true,
        }),
        summary: Some(HardenedSummaryReport {
            hardened_obligations,
            proved_hardened_obligations,
            inventory_entries,
            model_assumptions,
            proof_evidence_entries,
        }),
        boundary_inventory,
    })
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum HardenedBoundaryIdentity {
    ExactClaim { function: String, kind: String, claim_digest_sha256: String },
    UniqueRow(usize),
}

fn hardened_boundary_identity(
    authority: Option<&AuthorizedRows<'_>>,
    index: usize,
    result: &VerificationResult,
) -> HardenedBoundaryIdentity {
    authority
        .filter(|authority| authority.authorizes_row(index, result))
        .and_then(|_| structured_transport_evidence(result))
        .and_then(|evidence| evidence.claim_digest_sha256)
        .filter(|digest| trust_types::digest::is_stable_sha256_hex(digest))
        .map(|claim_digest_sha256| HardenedBoundaryIdentity::ExactClaim {
            function: result.function.clone(),
            kind: result.kind.clone(),
            claim_digest_sha256,
        })
        .unwrap_or(HardenedBoundaryIdentity::UniqueRow(index))
}

fn hardened_inventory_entry(
    result: &VerificationResult,
    category: &str,
    boundary: &str,
    obligation_id: Option<String>,
) -> HardenedBoundaryInventoryEntry {
    HardenedBoundaryInventoryEntry {
        id: obligation_id.as_ref().map(|id| format!("hardened-inventory:{id}")),
        role: HardenedBoundaryInventoryRole::Inventory,
        category: category.to_string(),
        boundary: boundary.to_string(),
        function: nonempty_owned(&result.function),
        description: nonempty_owned(&result.message),
        location: result.location.clone(),
        obligation_id,
        proof_evidence_id: None,
        source: display_backend(&result.backend).map(str::to_string),
    }
}

fn hardened_model_assumption_entries(
    index: usize,
    result: &VerificationResult,
    category: &str,
    boundary: &str,
    obligation_id: Option<String>,
    structured: Option<&crate::types::StructuredTransportEvidence>,
) -> Vec<HardenedBoundaryInventoryEntry> {
    let mut entries = Vec::new();

    if let Some(reason) =
        result.reason.as_deref().filter(|reason| hardened_text_is_model_assumption(reason))
    {
        entries.push(hardened_model_assumption_entry(
            result,
            category,
            boundary,
            obligation_id.clone(),
            display_backend(&result.backend).map(str::to_string),
            Some(format!("reason-{index}")),
            reason.to_string(),
        ));
    }

    let Some(structured) = structured else {
        return entries;
    };

    if let Some(native_trust_ir) = &structured.native_trust_ir {
        for (diagnostic_index, diagnostic) in native_trust_ir.diagnostics.iter().enumerate() {
            if let Some((boundary, description)) = hardened_model_assumption_diagnostic(diagnostic)
            {
                entries.push(hardened_model_assumption_entry(
                    result,
                    category,
                    &boundary,
                    obligation_id.clone(),
                    nonempty_owned(&native_trust_ir.backend),
                    Some(format!("native-{index}-{diagnostic_index}")),
                    description,
                ));
            }
        }
    }

    if let Some(proof) = &structured.proof_evidence {
        for (diagnostic_index, diagnostic) in proof.diagnostics.iter().enumerate() {
            if let Some((boundary, description)) = hardened_model_assumption_diagnostic(diagnostic)
            {
                entries.push(hardened_model_assumption_entry(
                    result,
                    category,
                    &boundary,
                    obligation_id.clone(),
                    nonempty_owned(&proof.backend),
                    Some(format!("proof-{index}-{diagnostic_index}")),
                    description,
                ));
            }
        }
    }

    entries
}

fn hardened_model_assumption_entry(
    result: &VerificationResult,
    category: &str,
    boundary: &str,
    obligation_id: Option<String>,
    source: Option<String>,
    id_suffix: Option<String>,
    description: String,
) -> HardenedBoundaryInventoryEntry {
    HardenedBoundaryInventoryEntry {
        id: hardened_model_assumption_entry_id(obligation_id.as_deref(), id_suffix.as_deref()),
        role: HardenedBoundaryInventoryRole::ModelAssumption,
        category: category.to_string(),
        boundary: boundary.to_string(),
        function: nonempty_owned(&result.function),
        description: Some(description),
        location: result.location.clone(),
        obligation_id,
        proof_evidence_id: None,
        source,
    }
}

fn hardened_model_assumption_diagnostic(
    diagnostic: &TransportEvidenceDiagnostic,
) -> Option<(String, String)> {
    let mut text = format!("{} {}", diagnostic.code, diagnostic.message);
    if let Some(detail) = diagnostic.detail.as_deref() {
        text.push(' ');
        text.push_str(detail);
    }
    if !hardened_text_is_model_assumption(&text) {
        return None;
    }

    let boundary =
        nonempty_owned(&diagnostic.code).unwrap_or_else(|| "hardened_model_assumption".to_string());
    let mut description = diagnostic.message.clone();
    if let Some(detail) = diagnostic.detail.as_deref().filter(|detail| !detail.trim().is_empty()) {
        description.push_str(" (");
        description.push_str(detail);
        description.push(')');
    }

    Some((boundary, description))
}

fn hardened_proof_evidence_entry(
    result: &VerificationResult,
    category: &str,
    boundary: &str,
    obligation_id: Option<String>,
    proof: &TransportProofEvidence,
) -> Option<HardenedBoundaryInventoryEntry> {
    if !result.outcome.is_proved() || proof.status != TransportProofStatus::Proved {
        return None;
    }

    // Every publishable proof has an identity at the proof-envelope boundary.
    // For CleanCic v2 that identity is content-addressed and the strict
    // publication predicate above requires `proof_id == artifact_id ==
    // clean-cic:v2:<sha256>`. Never recover a missing envelope identity from an
    // artifact: doing so would silently weaken that binding at hardened-inventory
    // publication time.
    let proof_evidence_id = proof.proof_id.clone()?;

    Some(HardenedBoundaryInventoryEntry {
        id: Some(format!("hardened-proof-evidence:{proof_evidence_id}")),
        role: HardenedBoundaryInventoryRole::ProofEvidence,
        category: category.to_string(),
        boundary: boundary.to_string(),
        function: nonempty_owned(&result.function),
        description: Some(hardened_proof_evidence_description(result, proof)),
        location: result.location.clone(),
        obligation_id,
        proof_evidence_id: Some(proof_evidence_id),
        source: nonempty_owned(&proof.backend),
    })
}

fn hardened_proof_evidence_description(
    result: &VerificationResult,
    proof: &TransportProofEvidence,
) -> String {
    let mut parts = vec![format!("structured proof evidence proved by {}", proof.backend)];
    if !proof.suite.trim().is_empty() {
        parts.push(format!("suite {}", proof.suite));
    }
    if let Some(request_id) = proof.request_id.as_deref().filter(|id| !id.trim().is_empty()) {
        parts.push(format!("request {request_id}"));
    }
    if !result.message.trim().is_empty() {
        parts.push(result.message.clone());
    }
    parts.join("; ")
}

fn hardened_boundary_item(result: &VerificationResult, category: &str) -> String {
    let marker = format!("hardened boundary ({category}):");
    if let Some(rest) = result.message.trim().strip_prefix(&marker) {
        let rest = rest.trim();
        let boundary = rest.split_once(": ").map_or(rest, |(boundary, _)| boundary).trim();
        if !boundary.is_empty() {
            return boundary.to_string();
        }
    }

    nonempty_owned(&result.function).unwrap_or_else(|| result.kind.clone())
}

fn hardened_model_assumption_entry_id(
    obligation_id: Option<&str>,
    suffix: Option<&str>,
) -> Option<String> {
    match (
        obligation_id.filter(|id| !id.trim().is_empty()),
        suffix.filter(|suffix| !suffix.trim().is_empty()),
    ) {
        (Some(obligation_id), Some(suffix)) => {
            Some(format!("hardened-model-assumption:{obligation_id}:{suffix}"))
        }
        (Some(obligation_id), None) => Some(format!("hardened-model-assumption:{obligation_id}")),
        (None, Some(suffix)) => Some(format!("hardened-model-assumption:{suffix}")),
        (None, None) => None,
    }
}

// `hardened_obligations` here is the E4-narrowed denominator: proved,
// non-mandate hardened rows only. So `proof_evidence_entries ==
// hardened_obligations` means every PROVED hardened boundary carries publishable
// native proof (proof_backed). A run whose only hardened rows are unknown/mandate
// has `hardened_obligations == 0` and reports "none" here — the terminal label is
// then driven by the outcome gate (INCONCLUSIVE), not an evidence FAIL.
fn hardened_assurance_level(hardened_obligations: usize, proof_evidence_entries: usize) -> String {
    if hardened_obligations > 0 && proof_evidence_entries == hardened_obligations {
        "proof_backed".to_string()
    } else if proof_evidence_entries > 0 {
        "partial_proof_evidence".to_string()
    } else if hardened_obligations > 0 {
        "inventory_only".to_string()
    } else {
        "none".to_string()
    }
}

const DEFAULT_HARDENED_PROFILE: &str = "unix_hardened";

fn hardened_profile_enabled_categories(
    profile_name: Option<&str>,
    observed_categories: &BTreeSet<String>,
) -> Vec<String> {
    match profile_name.map(str::trim).filter(|profile| !profile.is_empty()) {
        Some(_) => all_hardened_category_tags(),
        _ => observed_categories.iter().cloned().collect(),
    }
}

fn all_hardened_category_tags() -> Vec<String> {
    [
        HardenedVcCategory::RawPathApi,
        HardenedVcCategory::PathIdentity,
        HardenedVcCategory::PermissionChange,
        HardenedVcCategory::PermissionCreate,
        HardenedVcCategory::PermissionWindow,
        HardenedVcCategory::Utf8Reject,
        HardenedVcCategory::ByteLoss,
        HardenedVcCategory::ErrorDiscard,
        HardenedVcCategory::PanicBoundary,
        HardenedVcCategory::CompatObservable,
        HardenedVcCategory::ProcessSemantics,
        HardenedVcCategory::TrustDomain,
        HardenedVcCategory::TrustDomainOrder,
        HardenedVcCategory::UnsafeOperation,
        HardenedVcCategory::FfiBoundary,
    ]
    .into_iter()
    .map(|category| category.as_tag().to_string())
    .collect()
}

fn detected_hardened_profile_name(diagnostics: &[CompilerDiagnostic]) -> Option<String> {
    diagnostics.iter().find_map(|diagnostic| extract_hardened_profile_name(&diagnostic.message))
}

fn extract_hardened_profile_name(message: &str) -> Option<String> {
    if let Some(rest) = message.split_once("hardened profile `").map(|(_, rest)| rest) {
        if let Some((profile, _)) = rest.split_once('`') {
            return nonempty_owned(profile);
        }
    }

    if let Some(rest) = message.split_once("TRUST_PROFILE=").map(|(_, rest)| rest) {
        let profile: String = rest
            .chars()
            .take_while(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '_' | '-' | '.'))
            .collect();
        return nonempty_owned(&profile);
    }

    None
}

fn hardened_text_is_model_assumption(text: &str) -> bool {
    let text = text.to_ascii_lowercase();
    text.contains("model assumption") || (text.contains("model") && text.contains("assumption"))
}

/// The compiler-provided design-mandate bit for this row, read from the
/// structured transport evidence. `false` for rows without structured
/// transport (text-parsed rows can never be excluded from the denominator —
/// targo must not guess mandates from text).
pub(crate) fn transport_design_mandate(result: &VerificationResult) -> bool {
    if !crate::types::structured_transport_vc_kind_is_authority_safe(result)
        || !structured_transport_evidence(result).is_some_and(|evidence| evidence.design_mandate)
    {
        return false;
    }

    // The bit is meaningful only for hardened-category VCs.  Bind a modern
    // row to its exact typed category, and preserve fieldless compatibility
    // only for tags in the explicit hardened namespace. Otherwise a
    // self-consistent DivisionByZero/Postcondition row with a stray bit could
    // be removed from the proof denominator as though it were a design-only mandate.
    match exact_transport_vc_kind(result) {
        Ok(Some(kind)) => kind.hardened_category().is_some(),
        Ok(None) => parse_hardened_category(&result.kind).is_some(),
        Err(()) => false,
    }
}

fn nonempty_owned(value: &str) -> Option<String> {
    let value = value.trim();
    (!value.is_empty()).then(|| value.to_string())
}

fn report_function_name(result: &VerificationResult) -> String {
    if result.function.is_empty() { result.kind.clone() } else { result.function.clone() }
}

struct PublishableNativeProofComponents<'a> {
    proof: &'a TransportProofEvidence,
    native_trust_ir: &'a TransportNativeTrustIrEvidence,
    strength: ProofStrength,
    evidence: ProofEvidence,
}

fn native_proof_evidence_report(
    result: &VerificationResult,
    structured: Option<&crate::types::StructuredTransportEvidence>,
    run_diagnostics: &[String],
    materialization_root: Option<&Path>,
) -> Option<ObligationProofEvidenceReport> {
    let publishable =
        publishable_native_proof_components(result, structured, materialization_root)?;
    let proof = publishable.proof;
    let native_trust_ir = publishable.native_trust_ir;

    let mut warnings = Vec::new();
    if let Some(reason) = result.reason.as_deref().filter(|reason| is_full_verifier_text(reason)) {
        push_unique(&mut warnings, reason.to_string());
    }
    push_transport_diagnostics(&mut warnings, &native_trust_ir.diagnostics);
    push_transport_diagnostics(&mut warnings, &proof.diagnostics);
    for diagnostic in run_diagnostics {
        push_unique(&mut warnings, diagnostic.clone());
    }

    let backend =
        if proof.backend.is_empty() { result.backend.clone() } else { proof.backend.clone() };
    let strength = publishable.strength;
    let evidence = publishable.evidence;

    Some(ObligationProofEvidenceReport {
        suite: Some(proof.suite.clone()),
        backend: backend.clone(),
        request_id: proof.request_id.clone(),
        proof_id: proof.proof_id.clone(),
        native_id: proof.native_id.clone(),
        status: Some(proof.status),
        provenance: ObligationEvidenceProvenanceReport::NativeBackend { verifier: backend },
        strength,
        evidence,
        proof_certificate: None,
        native_trust_ir: Some(native_trust_ir.clone()),
        artifacts: proof.artifacts.clone(),
        diagnostics: proof.diagnostics.clone(),
        solver_warnings: (!warnings.is_empty()).then_some(warnings),
    })
}

fn kernel_proof_evidence_report(
    result: &VerificationResult,
    structured: Option<&crate::types::StructuredTransportEvidence>,
) -> Option<ObligationProofEvidenceReport> {
    let proof = structured?.proof_evidence.as_ref()?;
    if !clean_cic_transport_proof_is_publishable(result, proof) {
        return None;
    }
    let strength = proof.strength.clone()?;
    let evidence = proof.evidence.clone()?;
    Some(ObligationProofEvidenceReport {
        suite: Some(proof.suite.clone()),
        backend: proof.backend.clone(),
        request_id: proof.request_id.clone(),
        proof_id: proof.proof_id.clone(),
        native_id: proof.native_id.clone(),
        status: Some(proof.status),
        provenance: ObligationEvidenceProvenanceReport::NativeBackend {
            verifier: proof.backend.clone(),
        },
        strength,
        evidence,
        proof_certificate: None,
        native_trust_ir: None,
        artifacts: proof.artifacts.clone(),
        diagnostics: proof.diagnostics.clone(),
        solver_warnings: None,
    })
}

fn clean_cic_transport_proof_is_publishable(
    result: &VerificationResult,
    proof: &TransportProofEvidence,
) -> bool {
    if !result.outcome.is_proved()
        || proof.status != TransportProofStatus::Proved
        || !proof.suite.eq_ignore_ascii_case("trust-certify")
        || !proof.backend.eq_ignore_ascii_case("clean-kernel")
        || proof.request_id.is_some()
        || proof.native_id.is_some()
        || proof.artifacts.len() != 1
        || !proof.strength.as_ref().is_some_and(|strength| {
            strength.reasoning == trust_types::ReasoningKind::Constructive
                && strength.assurance == trust_types::AssuranceLevel::Certified
        })
        || !proof.evidence.as_ref().is_some_and(|evidence| {
            evidence.reasoning == trust_types::ReasoningKind::Constructive
                && evidence.assurance == trust_types::AssuranceLevel::Certified
        })
        || !proof.diagnostics.is_empty()
    {
        return false;
    }

    let artifact = &proof.artifacts[0];
    let Some(metadata) = artifact.metadata.as_ref() else {
        return false;
    };
    // Content addressing binds bytes; it does not by itself establish that
    // those bytes are a CleanCic certificate. Decode the exact TrustIr type and
    // require a canonical value round-trip so unknown/ignored JSON fields cannot
    // acquire publication authority merely by being hashed under this domain.
    let Ok(decoded) = serde_json::from_value::<trust_ir::ProofEvidence>(metadata.clone()) else {
        return false;
    };
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = &decoded else {
        return false;
    };
    if term.is_empty()
        || context.is_empty()
        || lineage.algorithm != trust_ir::ProofDigestAlgorithm::Sha256
        || lineage.is_zero()
        || serde_json::to_value(&decoded).ok().as_ref() != Some(metadata)
    {
        return false;
    }
    let Ok(bytes) = serde_json::to_vec(metadata) else {
        return false;
    };
    let digest = trustc_domain_length_bound_sha256_hex("trustc.transport-clean-cic.v2", &bytes);
    let expected_id = format!("clean-cic:v2:{digest}");
    artifact.kind == "clean_cic"
        && artifact.format.as_deref() == Some("trust-ir-cleancic-v2")
        && artifact.materialization.is_none()
        && artifact
            .digest
            .as_ref()
            .is_some_and(|declared| declared.algorithm == "sha256" && declared.value == digest)
        && proof.proof_id.as_deref() == Some(expected_id.as_str())
        && artifact.artifact_id.as_deref() == proof.proof_id.as_deref()
        && artifact.uri.as_deref() == Some(&format!("trust-certify://clean-cic/{digest}"))
}

fn trustc_domain_length_bound_sha256_hex(domain: &str, payload: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(b"trustc.digest-frame.v1");
    digest.update((domain.len() as u64).to_be_bytes());
    digest.update(domain.as_bytes());
    digest.update((payload.len() as u64).to_be_bytes());
    digest.update(payload);
    trust_types::digest::lowercase_hex(&digest.finalize())
}

/// Structural publication contract expected from an authenticated compiler
/// Proved row.  The caller still needs live channel authority; this predicate
/// merely ensures the row has the exact native or clean-kernel evidence shape
/// that the canonical report can attach, so terminal counts cannot outrun JSON.
pub(crate) fn authenticated_proved_row_has_publication_evidence(
    result: &VerificationResult,
    materialization_root: Option<&Path>,
) -> bool {
    let structured = structured_transport_evidence(result);
    native_proof_evidence_report(result, structured.as_ref(), &[], materialization_root).is_some()
        || kernel_proof_evidence_report(result, structured.as_ref()).is_some()
}

/// A hardened boundary discharged by the clean CIC KERNEL (`certify_vc`) carries
/// no native TrustIR envelope (it is a zero-trust kernel refutation, not a native
/// solver run), so `publishable_native_proof_components` — which requires
/// `structured.native_trust_ir` — rejects it. But a kernel-certified clean_cic
/// proof is the STRONGEST evidence a hardened obligation can carry, so recognize
/// it as publishable hardened proof evidence, gated by the IDENTICAL strict
/// `clean_cic_transport_proof_is_publishable` contract the general report path
/// uses via `kernel_proof_evidence_report`. Returns the borrowed transport proof
/// so the caller mints the same `hardened_proof_evidence_entry` as the native path.
fn publishable_clean_cic_hardened_proof<'a>(
    result: &VerificationResult,
    structured: Option<&'a crate::types::StructuredTransportEvidence>,
) -> Option<&'a TransportProofEvidence> {
    let proof = structured?.proof_evidence.as_ref()?;
    clean_cic_transport_proof_is_publishable(result, proof).then_some(proof)
}

/// Select either publication-grade native evidence or the stricter
/// content-addressed clean-CIC kernel evidence for one hardened boundary.
///
/// This helper is deliberately shared by representative selection (both the
/// incoming and existing row checks) and inventory emission. Otherwise a
/// clean-CIC duplicate can be recognized when minting evidence but lose the
/// boundary representative election to an earlier evidence-less twin.
fn publishable_hardened_proof<'a>(
    result: &VerificationResult,
    structured: Option<&'a crate::types::StructuredTransportEvidence>,
    materialization_root: Option<&Path>,
) -> Option<&'a TransportProofEvidence> {
    publishable_native_proof_components(result, structured, materialization_root)
        .map(|components| components.proof)
        .or_else(|| publishable_clean_cic_hardened_proof(result, structured))
}

fn publishable_native_proof_components<'a>(
    result: &VerificationResult,
    structured: Option<&'a crate::types::StructuredTransportEvidence>,
    materialization_root: Option<&Path>,
) -> Option<PublishableNativeProofComponents<'a>> {
    let structured = structured?;
    let proof = structured.proof_evidence.as_ref()?;
    let native_trust_ir = structured.native_trust_ir.as_ref()?;
    if !structured_native_proof_is_publishable(
        result,
        proof,
        native_trust_ir,
        structured.obligation_id.as_deref(),
        materialization_root,
    ) {
        return None;
    }

    let strength = proof.strength.clone()?;
    let evidence = proof.evidence.clone()?;
    Some(PublishableNativeProofComponents { proof, native_trust_ir, strength, evidence })
}

fn native_transport_evidence(
    structured: &crate::types::StructuredTransportEvidence,
) -> Option<ObligationTransportEvidenceReport> {
    (structured.obligation_id.is_some()
        || structured.claim_digest_sha256.is_some()
        || structured.typed_kind.is_some()
        || structured.native_trust_ir.is_some()
        || structured.proof_evidence.is_some()
        || structured.monitor.is_some())
    .then(|| ObligationTransportEvidenceReport {
        obligation_id: structured.obligation_id.clone(),
        claim_digest_sha256: structured.claim_digest_sha256.clone(),
        typed_kind: structured.typed_kind.clone(),
        native_trust_ir: structured.native_trust_ir.clone(),
        proof_evidence: structured.proof_evidence.clone(),
        monitor: structured.monitor.clone(),
    })
}

fn structured_native_proof_is_publishable(
    result: &VerificationResult,
    proof: &TransportProofEvidence,
    native_trust_ir: &TransportNativeTrustIrEvidence,
    obligation_id: Option<&str>,
    materialization_root: Option<&Path>,
) -> bool {
    let canonical_suite = proof.suite.trim().to_ascii_lowercase();
    let canonical_identity =
        matches!(canonical_suite.as_str(), "trust-wp" | "trust-mc" | "trust-vc")
            && proof.request_id.as_deref().is_some_and(nonempty)
            && proof.proof_id.as_deref().is_some_and(nonempty)
            && proof.native_id.as_deref().is_some_and(|native_id| {
                native_id
                    == format!(
                        "trust_ir-native-{canonical_suite}-request-{}-proof-{}",
                        proof.request_id.as_deref().unwrap_or_default(),
                        proof.proof_id.as_deref().unwrap_or_default(),
                    )
            });
    let binding_matches_native_id = proof.native_id.as_deref().is_some_and(|native_id| {
        proof.artifacts.iter().all(|artifact| {
            artifact
                .materialization
                .as_ref()
                .is_none_or(|materialization| materialization.proof_binding_id == native_id)
        })
    });
    let proof_topology_valid = materialization_root.map_or_else(
        || {
            trust_types::transport_proof_artifact_topology_defect(
                &proof.suite,
                &proof.artifacts,
                obligation_id,
            )
            .is_none()
        },
        |root| {
            trust_types::transport_proof_artifact_topology_defect_at_root(
                &proof.suite,
                &proof.artifacts,
                obligation_id,
                root,
            )
            .is_none()
        },
    );
    let native_shape_valid = materialization_root.map_or_else(
        || native_trust_ir_artifact_shape_is_publishable(native_trust_ir),
        |root| native_trust_ir_artifact_shape_is_publishable_at_root(native_trust_ir, root),
    );
    result.outcome.is_proved()
        && proof.status == TransportProofStatus::Proved
        && canonical_identity
        && proof.backend.trim().eq_ignore_ascii_case(&canonical_suite)
        && binding_matches_native_id
        && proof.strength.as_ref().is_some_and(proof_strength_is_publication_grade)
        && proof.evidence.as_ref().is_some_and(proof_evidence_is_publication_grade)
        && proof.strength.as_ref().is_some_and(|strength| {
            proof.evidence.as_ref() == Some(&ProofEvidence::from(strength.clone()))
        })
        && proof_topology_valid
        && transport_diagnostics_are_publishable(&proof.diagnostics)
        && native_trust_ir.present
        && native_trust_ir.suite.trim().eq_ignore_ascii_case(&canonical_suite)
        && native_trust_ir.backend.trim().eq_ignore_ascii_case(&canonical_suite)
        && native_shape_valid
        && transport_diagnostics_are_publishable(&native_trust_ir.diagnostics)
        && native_trust_ir.request_id.as_deref() == proof.request_id.as_deref()
        && native_trust_ir.native_id.as_deref() == proof.native_id.as_deref()
}

/// Apply the exact publication-grade native-proof contract to one compiler
/// transport row.  Consumers that retain typed transport (notably the
/// self-verification harness) must use this predicate instead of reconstructing
/// a weaker approximation from JSON field names.
pub(crate) fn transport_obligation_has_publishable_native_proof(
    transport: &trust_types::TransportObligationResult,
    materialization_root: &Path,
) -> bool {
    let result = transport_to_verification_result("<typed-transport>", transport);
    let Some(proof) = transport.proof_evidence.as_ref() else {
        return false;
    };
    let Some(native_trust_ir) = transport.native_trust_ir.as_ref() else {
        return false;
    };
    structured_native_proof_is_publishable(
        &result,
        proof,
        native_trust_ir,
        transport.obligation_id.as_deref(),
        Some(materialization_root),
    )
}

fn proof_strength_is_publication_grade(strength: &ProofStrength) -> bool {
    !strength.is_bounded()
        && strength.reasoning.is_complete()
        && strength.assurance.meets_reporting_floor()
}

fn proof_evidence_is_publication_grade(evidence: &ProofEvidence) -> bool {
    !evidence.is_bounded()
        && evidence.reasoning.is_complete()
        && evidence.assurance.meets_reporting_floor()
}

pub(crate) fn is_solver_transcript_artifact(artifact: &TransportEvidenceArtifact) -> bool {
    let kind = normalized_artifact_kind(&artifact.kind);
    matches!(
        kind.as_str(),
        "solver_transcript" | "smt_transcript" | "smtlib_transcript" | "solver_transcript_log"
    )
}

pub(crate) fn is_replay_or_check_artifact(artifact: &TransportEvidenceArtifact) -> bool {
    let kind = normalized_artifact_kind(&artifact.kind);
    matches!(
        kind.as_str(),
        "proof_replay"
            | "proof_replay_trace"
            | "replay_log"
            | "machine_replay"
            | "machine_code_replay"
            | "proof_check"
            | "proof_check_report"
            | "checked_proof_report"
            | "checked_report"
            | "checker_report"
            | "certificate"
            | "proof_certificate"
            | "checked_certificate"
    )
}

fn normalized_artifact_kind(kind: &str) -> String {
    let mut normalized = String::new();
    let mut previous_was_lower_or_digit = false;
    let mut previous_was_separator = false;

    for ch in kind.trim().chars() {
        if ch.is_ascii_alphanumeric() {
            if ch.is_ascii_uppercase() {
                if !normalized.is_empty() && !previous_was_separator && previous_was_lower_or_digit
                {
                    normalized.push('_');
                }
                normalized.push(ch.to_ascii_lowercase());
                previous_was_lower_or_digit = false;
            } else {
                normalized.push(ch.to_ascii_lowercase());
                previous_was_lower_or_digit = ch.is_ascii_lowercase() || ch.is_ascii_digit();
            }
            previous_was_separator = false;
        } else if !normalized.is_empty() && !previous_was_separator {
            normalized.push('_');
            previous_was_lower_or_digit = false;
            previous_was_separator = true;
        }
    }

    while normalized.ends_with('_') {
        normalized.pop();
    }

    normalized
}

fn transport_diagnostics_are_publishable(diagnostics: &[TransportEvidenceDiagnostic]) -> bool {
    diagnostics.iter().all(|diagnostic| {
        matches!(
            diagnostic.severity,
            TransportEvidenceDiagnosticSeverity::Info
                | TransportEvidenceDiagnosticSeverity::Warning
        )
    })
}

fn nonempty(value: &str) -> bool {
    !value.trim().is_empty()
}

fn push_transport_diagnostics(
    warnings: &mut Vec<String>,
    diagnostics: &[TransportEvidenceDiagnostic],
) {
    for diagnostic in diagnostics {
        let severity = match diagnostic.severity {
            TransportEvidenceDiagnosticSeverity::Info => "info",
            TransportEvidenceDiagnosticSeverity::Warning => "warning",
            TransportEvidenceDiagnosticSeverity::Error => "error",
            _ => "unknown",
        };
        let mut message = format!("{severity}: {}: {}", diagnostic.code, diagnostic.message);
        if let Some(detail) = diagnostic.detail.as_deref().filter(|detail| !detail.is_empty()) {
            message.push_str(" (");
            message.push_str(detail);
            message.push(')');
        }
        push_unique(warnings, message);
    }
}

fn append_full_verifier_diagnostics_to_reason(reason: &mut String, run_diagnostics: &[String]) {
    for diagnostic in run_diagnostics {
        if !reason.contains(diagnostic) {
            if !reason.is_empty() {
                reason.push_str("; ");
            }
            reason.push_str(diagnostic);
        }
    }
}

fn full_verifier_terminal_lines(
    results: &[VerificationResult],
    diagnostics: &[CompilerDiagnostic],
) -> Vec<String> {
    let full_results: Vec<&VerificationResult> =
        results.iter().filter(|result| is_full_verifier_result(result)).collect();
    let full_diagnostics = native_full_verifier_diagnostics(diagnostics);
    if full_results.is_empty() && full_diagnostics.is_empty() {
        return Vec::new();
    }

    let proved = full_results.iter().filter(|result| result.outcome.is_proved()).count();
    let failed = full_results.iter().filter(|result| result.outcome.is_failed()).count();
    let runtime_checked =
        full_results.iter().filter(|result| result.outcome.is_runtime_checked()).count();
    let inconclusive =
        full_results.iter().filter(|result| result.outcome.is_inconclusive()).count();

    let mut lines = Vec::new();
    lines.push("Native full verifier evidence:".to_string());
    if !full_results.is_empty() {
        lines.push(format!(
            "  Transport obligations: {} ({} proved, {} failed, {} runtime-checked, {} inconclusive)",
            full_results.len(),
            proved,
            failed,
            runtime_checked,
            inconclusive
        ));
    }
    for diagnostic in full_diagnostics.iter().take(6) {
        lines.push(format!("  Diagnostic: {diagnostic}"));
    }
    if full_diagnostics.len() > 6 {
        lines
            .push(format!("  ... {} more full-verifier diagnostic(s)", full_diagnostics.len() - 6));
    }
    lines
}

fn native_full_verifier_diagnostics(diagnostics: &[CompilerDiagnostic]) -> Vec<String> {
    diagnostics
        .iter()
        .filter(|diagnostic| is_full_verifier_text(&diagnostic.message))
        .map(|diagnostic| diagnostic.message.clone())
        .collect()
}

fn is_full_verifier_result(result: &VerificationResult) -> bool {
    is_full_verifier_backend(&result.backend)
        || is_full_verifier_text(&result.message)
        || is_full_verifier_text(&result.kind)
        || result.reason.as_deref().is_some_and(is_full_verifier_text)
}

fn is_full_verifier_backend(backend: &str) -> bool {
    let backend = backend.trim();
    backend == "trust-full-verifier" || backend.contains("full-verifier")
}

fn is_full_verifier_text(text: &str) -> bool {
    let text = text.to_ascii_lowercase();
    text.contains("native full verifier")
        || text.contains("trust-full-verifier")
        || text.contains("fullverification::")
        || text.contains("trust full verification failed")
        || text.contains("trust-verify-full")
}

fn push_unique(values: &mut Vec<String>, value: String) {
    if !values.iter().any(|existing| existing == &value) {
        values.push(value);
    }
}

/// Parse a VC kind tag string back to a `VcKind`.
///
/// Only fieldless kinds are reconstructed. A compact tag that discarded typed
/// fields maps to `UnsupportedMir`, never to a fabricated variant or to an
/// `Assertion` with a runtime fallback.
pub(crate) fn parse_vc_kind(kind: &str) -> VcKind {
    if let Some(kind) = parse_exact_legacy_vc_kind(kind, kind) {
        return kind;
    }
    if crate::types::compact_vc_tag_requires_typed_kind(kind) {
        return VcKind::UnsupportedMir {
            kind: kind.to_string(),
            detail: "legacy compact VC tag omitted its typed payload".to_string(),
        };
    }
    VcKind::Assertion { message: kind.to_string() }
}

/// Backward-compatible decoder for kinds whose complete semantic fields are
/// present in the compact tag/description pair. New compiler transport carries
/// `typed_kind` and does not depend on this compatibility path.
fn parse_exact_legacy_vc_kind(kind: &str, description: &str) -> Option<VcKind> {
    match kind {
        "divzero" | "div_by_zero" | "division_by_zero" => Some(VcKind::DivisionByZero),
        "remzero" | "remainder_by_zero" => Some(VcKind::RemainderByZero),
        "index_out_of_bounds" | "bounds" => Some(VcKind::IndexOutOfBounds),
        "slice" | "slice_bounds_check" => Some(VcKind::SliceBoundsCheck),
        "assert" | "assertion" => Some(VcKind::Assertion {
            message: description.strip_prefix("assertion: ").unwrap_or(description).to_string(),
        }),
        "precond" | "precondition" => {
            let callee = exact_delimited_payload(description, "precondition of `", "`")?;
            Some(VcKind::Precondition { callee: callee.to_string() })
        }
        "postcond" | "postcondition" => Some(VcKind::Postcondition),
        "unreach" | "unreachable" => Some(VcKind::Unreachable),
        "deadstate" | "dead_state" => {
            let state = exact_delimited_payload(description, "dead state `", "`")?;
            Some(VcKind::DeadState { state: state.to_string() })
        }
        "deadlock" => Some(VcKind::Deadlock),
        "float_division_by_zero" => Some(VcKind::FloatDivisionByZero),
        s if parse_hardened_category(s).is_some() => {
            let category = parse_hardened_category(s).expect("checked by match guard");
            Some(VcKind::HardenedBoundary {
                category,
                callee: kind.to_string(),
                detail: format!("hardened verification category {}", category.as_tag()),
            })
        }
        // Trust (assumption ledger): an `assumption:<tag>` row is a recorded
        // unverified assumption, NOT a runtime-checked obligation. Folding it
        // to `Assertion` (the default arm) gives it a runtime fallback
        // (`vc_kind.rs` has_runtime_fallback = true), so `RuntimeCheckPolicy::
        // Auto` relabels it `RuntimeChecked` in report.json — a lie (the async
        // coroutine gap has no runtime check). `UnsupportedMir` has no runtime
        // fallback, so the row stays Unknown/Inconclusive as it must.
        s if s.starts_with("assumption:") => {
            Some(VcKind::UnsupportedMir { kind: s.to_string(), detail: description.to_string() })
        }
        _ => None,
    }
}

fn exact_delimited_payload<'a>(value: &'a str, prefix: &str, suffix: &str) -> Option<&'a str> {
    let payload = value.strip_prefix(prefix)?.strip_suffix(suffix)?;
    (!payload.is_empty()
        && !payload.contains('`')
        && !payload.chars().any(char::is_control)
        && payload.trim() == payload)
        .then_some(payload)
}

fn parse_hardened_category(kind: &str) -> Option<HardenedVcCategory> {
    let tag = kind
        .strip_prefix("hardened_")
        .or_else(|| kind.strip_prefix("hardened::"))
        .or_else(|| kind.strip_prefix("hardened:"))?;
    let normalized = normalize_hardened_category_tag(tag);
    HardenedVcCategory::from_tag(&normalized)
}

fn normalize_hardened_category_tag(tag: &str) -> String {
    match tag {
        "path" => "raw_path_api".to_string(),
        "bytes" => "byte_loss".to_string(),
        "utf8" => "utf8_reject".to_string(),
        "error" => "error_discard".to_string(),
        "panic" => "panic_boundary".to_string(),
        "trust" => "trust_domain".to_string(),
        "trust-order" => "trust_domain_order".to_string(),
        "compat" => "compat_observable".to_string(),
        "process" => "process_semantics".to_string(),
        "unsafe" => "unsafe_operation".to_string(),
        "ffi" | "unsafe-ffi" => "ffi_boundary".to_string(),
        tag => tag.replace('-', "_"),
    }
}

/// Minimal HTML escaping for report-output regression fixtures.
#[cfg(test)]
pub(crate) fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;").replace('"', "&quot;")
}

fn plural_s(n: usize) -> &'static str {
    if n == 1 { "" } else { "s" }
}

fn terminal_result_line(result: &VerificationResult) -> String {
    // Trust (green front door, Stage 2): an `assumption:*` row is a recorded
    // unverified assumption, not an outcome the solver returned — render it as
    // ASSUMED so the terminal never displays it as UNKNOWN (or, for a defective
    // row, as PROVED). Display-only: the wire `VerificationOutcome` is
    // untouched, and the partition still counts a defective row as unknown.
    let label =
        if result.kind.starts_with("assumption:") { "ASSUMED" } else { result.outcome.label() };
    format!(
        "  [{}] [{}] {}{}",
        label,
        result.kind,
        result.message,
        terminal_result_detail_suffix(result)
    )
}

fn terminal_result_detail_suffix(result: &VerificationResult) -> String {
    let location = result.location.as_ref().and_then(format_terminal_location);
    let solver_details = terminal_solver_detail(result);

    match (location, solver_details) {
        (Some(location), Some(details)) => format!(" @ {location} ({details})"),
        (Some(location), None) => format!(" @ {location}"),
        (None, Some(details)) => format!(" ({details})"),
        (None, None) => String::new(),
    }
}

fn terminal_solver_detail(result: &VerificationResult) -> Option<String> {
    match (display_backend(&result.backend), result.time_ms) {
        (Some(backend), Some(time_ms)) => Some(format!("{backend}, {time_ms}ms")),
        (Some(backend), None) => Some(backend.to_string()),
        (None, Some(time_ms)) => Some(format!("{time_ms}ms")),
        (None, None) => None,
    }
}

fn format_terminal_location(span: &SourceSpan) -> Option<String> {
    if let Some(address) = span.binary_address_value() {
        return Some(format!("binary:0x{address:x}"));
    }

    let file = span.file.trim();
    if file.is_empty() {
        return None;
    }

    if span.line_start == 0 {
        return Some(file.to_string());
    }

    if span.col_start == 0 {
        return Some(format!("{file}:{}", span.line_start));
    }

    if span.line_end == 0 || (span.line_end == span.line_start && span.col_end <= span.col_start) {
        return Some(format!("{file}:{}:{}", span.line_start, span.col_start));
    }

    if span.line_end == span.line_start {
        return Some(format!("{file}:{}:{}-{}", span.line_start, span.col_start, span.col_end));
    }

    Some(format!(
        "{file}:{}:{}-{}:{}",
        span.line_start, span.col_start, span.line_end, span.col_end
    ))
}

fn display_backend(backend: &str) -> Option<&str> {
    let backend = backend.trim();
    (!backend.is_empty() && backend != "unknown").then_some(backend)
}

#[derive(Debug)]
struct UnsafeMemoryReportPreflight {
    repo_root: PathBuf,
    candidate_commit: String,
    candidate_tree: String,
    coverage: ProofUnsafeMemoryCoverage,
}

fn preflight_unsafe_memory_report(
    request: &UnsafeMemoryReportRequest,
    report: &VerificationReport,
) -> io::Result<UnsafeMemoryReportPreflight> {
    let requested_root = request.repo_root.canonicalize()?;
    let repo_root =
        crate::controlled_git::resolve_repo_root(&requested_root).map_err(io::Error::other)?;
    if repo_root != requested_root {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "unsafe-memory report repository root must name the exact Git top level {}; got {}",
                repo_root.display(),
                requested_root.display()
            ),
        ));
    }
    let candidate_commit = git_stdout(&repo_root, &["rev-parse", "--verify", "HEAD^{commit}"])?;
    if !is_full_git_sha(&candidate_commit) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("candidate commit must be a full git SHA, got `{candidate_commit}`"),
        ));
    }
    let candidate_tree = git_stdout(&repo_root, &["rev-parse", "HEAD^{tree}"])?;
    if !is_full_git_sha(&candidate_tree) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "candidate HEAD tree must be a full Git SHA",
        ));
    }

    let status = git_status_porcelain_lines(&repo_root)?;
    if !status.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "repo must be clean before emitting {PROOF_UNSAFE_MEMORY_REPORT_SCHEMA}; git status has {} entr{}",
                status.len(),
                if status.len() == 1 { "y" } else { "ies" }
            ),
        ));
    }

    let coverage = unsafe_memory_coverage(report)?;
    Ok(UnsafeMemoryReportPreflight { repo_root, candidate_commit, candidate_tree, coverage })
}

impl UnsafeMemoryReportPreflight {
    fn revalidate_source_snapshot(&self, report_output_root: Option<&Path>) -> io::Result<()> {
        let commit = git_stdout(&self.repo_root, &["rev-parse", "HEAD"])?;
        let tree = git_stdout(&self.repo_root, &["rev-parse", "HEAD^{tree}"])?;
        let output_exclusion = report_output_root
            .map(|output_root| self.validated_output_exclusion(output_root))
            .transpose()?
            .flatten();
        let status =
            git_status_porcelain_lines_excluding(&self.repo_root, output_exclusion.as_deref())?;
        if commit != self.candidate_commit || tree != self.candidate_tree || !status.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "unsafe-memory source snapshot changed during report publication",
            ));
        }
        Ok(())
    }

    fn validated_output_exclusion(&self, output_root: &Path) -> io::Result<Option<String>> {
        let repo_root = self.repo_root.canonicalize()?;
        let output_root = output_root.canonicalize()?;
        let Ok(relative) = output_root.strip_prefix(&repo_root) else {
            return Ok(None);
        };
        if relative.as_os_str().is_empty() || relative.starts_with(".git") {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "unsafe-memory report output must not cover the repository root or Git metadata",
            ));
        }
        let relative = relative.to_str().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "unsafe-memory report output path must be valid UTF-8 when it is inside the source repository",
            )
        })?;
        let tracked = git_stdout(&repo_root, &["ls-files", "--", relative])?;
        if !tracked.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "unsafe-memory report output must not contain tracked source files",
            ));
        }
        Ok(Some(relative.replace('\\', "/")))
    }
}

fn unsafe_memory_coverage(report: &VerificationReport) -> io::Result<ProofUnsafeMemoryCoverage> {
    let mut total = 0_u64;
    let mut proved = 0_u64;
    let mut blockers = Vec::new();
    let authorized_rows = report.complete_authorized_rows();

    for (index, result) in report.results.iter().enumerate() {
        if !is_unsafe_memory_result(result) {
            continue;
        }
        total += 1;
        if unsafe_memory_result_has_forbidden_marker(result) {
            blockers.push(format!(
                "{}:{} contains manual/stub/demo evidence markers",
                report_function_name(result),
                result.kind
            ));
            continue;
        }

        let structured = structured_transport_evidence(result);
        let structurally_publishable = publishable_native_proof_components(
            result,
            structured.as_ref(),
            report.proof_artifact_root.as_deref(),
        )
        .is_some();
        let live_authorized = authorized_rows
            .as_ref()
            .is_some_and(|authority| authority.authorizes_proved_row(index, result));
        if structurally_publishable && live_authorized {
            proved += 1;
        } else {
            blockers.push(format!(
                "{}:{} {}",
                report_function_name(result),
                result.kind,
                if structurally_publishable {
                    "lacks live authenticated compiler transport authority"
                } else {
                    "lacks publishable structured native proof evidence"
                }
            ));
        }
    }

    if !report.success {
        blockers.push(
            "full-verifier report did not pass; unsafe-memory wrapper requires a successful native proof report"
                .to_string(),
        );
    }
    if total == 0 {
        blockers.push(
            "no unsafe-memory obligations were emitted by the full-verifier report".to_string(),
        );
    }
    if proved != total {
        blockers.push(format!(
            "unsafe-memory obligations must be fully proved with structured native evidence, got {proved}/{total}"
        ));
    }

    if !blockers.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("unsafe-memory proof wrapper rejected: {}", blockers.join("; ")),
        ));
    }

    Ok(ProofUnsafeMemoryCoverage {
        unsafe_blocks_total: total,
        unsafe_blocks_proved: proved,
        unsafe_operations_total: total,
        unsafe_operations_proved: proved,
        memory_obligations_total: total,
        memory_obligations_proved: proved,
    })
}

fn is_unsafe_memory_result(result: &VerificationResult) -> bool {
    [
        result.kind.as_str(),
        result.message.as_str(),
        result.backend.as_str(),
        result.reason.as_deref().unwrap_or_default(),
    ]
    .iter()
    .any(|value| unsafe_memory_text(value))
        || structured_transport_evidence(result).is_some_and(|structured| {
            structured.obligation_id.as_deref().is_some_and(unsafe_memory_text)
                || structured.native_trust_ir.as_ref().is_some_and(|native| {
                    unsafe_memory_text(&native.suite) || unsafe_memory_text(&native.backend)
                })
                || structured.proof_evidence.as_ref().is_some_and(|proof| {
                    unsafe_memory_text(&proof.suite) || unsafe_memory_text(&proof.backend)
                })
        })
}

fn unsafe_memory_text(value: &str) -> bool {
    let value = value.to_ascii_lowercase();
    value.contains("unsafe")
        || value.contains("memory_safety")
        || value.contains("memory safety")
        || value.contains("raw_pointer")
        || value.contains("raw pointer")
        || value.contains("aliasing")
        || value.contains("provenance")
}

fn unsafe_memory_result_has_forbidden_marker(result: &VerificationResult) -> bool {
    [
        result.kind.as_str(),
        result.message.as_str(),
        result.backend.as_str(),
        result.reason.as_deref().unwrap_or_default(),
        result.raw_line.as_str(),
    ]
    .iter()
    .any(|value| proof_evidence_text_has_forbidden_marker(value))
}

fn proof_evidence_text_has_forbidden_marker(value: &str) -> bool {
    let value = value.to_ascii_lowercase();
    value.contains("manual")
        || value.contains("manual_pass")
        || value.contains("stub")
        || value.contains("demo")
        || value.contains("synthetic")
}

fn report_artifact_path(output_dir: &Path, artifact: ReportArtifact) -> PathBuf {
    output_dir.join(artifact.file_name())
}

#[cfg(test)]
fn write_report_artifacts(
    report: &trust_types::JsonProofReport,
    output_dir: &Path,
    html_report: &str,
) -> io::Result<()> {
    write_report_artifacts_from_root(report, output_dir, html_report, None, None, None)
}

fn write_report_artifacts_from_root(
    report: &trust_types::JsonProofReport,
    output_dir: &Path,
    html_report: &str,
    source_root: Option<&Path>,
    unsafe_memory_preflight: Option<UnsafeMemoryReportPreflight>,
    sealed_canonical_json: Option<&[u8]>,
) -> io::Result<()> {
    let output_root = preflight_report_output_root(output_dir)?;
    if let Some(preflight) = unsafe_memory_preflight.as_ref() {
        preflight.revalidate_source_snapshot(Some(&output_root))?;
    }
    let staged = tempfile::Builder::new()
        .prefix(".trust-report-stage-")
        .tempdir_in(&output_root)
        .map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("could not create private report staging directory: {error}"),
        )
    })?;
    persist_report_artifact_store(report, source_root, staged.path())?;
    trust_report::write_ndjson_report(report, staged.path()).map_err(|error| {
        io::Error::new(error.kind(), format!("failed to stage NDJSON report: {error}"))
    })?;
    let ndjson_len =
        std::fs::metadata(report_artifact_path(staged.path(), ReportArtifact::Ndjson))?.len();
    if ndjson_len > crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES as u64 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "NDJSON report exceeds the {}-byte saved-report limit",
                crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES
            ),
        ));
    }
    if html_report.len() > crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES.saturating_mul(4) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "HTML report exceeds the bounded rendered-report limit",
        ));
    }
    std::fs::write(report_artifact_path(staged.path(), ReportArtifact::Html), html_report)
        .map_err(|error| {
            io::Error::new(error.kind(), format!("failed to stage HTML report: {error}"))
        })?;
    let owned_canonical_json;
    let canonical_json = if let Some(serialized) = sealed_canonical_json {
        serialized
    } else {
        owned_canonical_json = serialize_canonical_report_bounded(report)?;
        &owned_canonical_json
    };
    std::fs::write(report_artifact_path(staged.path(), ReportArtifact::Json), canonical_json)
        .map_err(|error| {
            io::Error::new(error.kind(), format!("failed to stage JSON report: {error}"))
        })?;
    if let Some(preflight) = unsafe_memory_preflight.as_ref() {
        preflight.revalidate_source_snapshot(Some(&output_root))?;
        write_unsafe_memory_report_wrapper(preflight, staged.path())?;
        preflight.revalidate_source_snapshot(Some(&output_root))?;
    }
    sync_report_bundle(staged.path())?;
    if let Some(preflight) = unsafe_memory_preflight.as_ref() {
        preflight.revalidate_source_snapshot(Some(&output_root))?;
    }
    commit_staged_report_bundle(staged.path(), &output_root)?;
    if let Some(preflight) = unsafe_memory_preflight.as_ref() {
        if let Err(error) = preflight.revalidate_source_snapshot(Some(&output_root)) {
            // The ordinary reports are observational, but the wrapper makes a
            // clean-source assertion. Remove that assertion if the source
            // changed in the final install window.
            remove_path_if_exists(
                &unsafe_memory_report_artifact_path(&output_root),
                "unsafe-memory report",
            )?;
            return Err(error);
        }
    }
    for artifact in [ReportArtifact::Ndjson, ReportArtifact::Html, ReportArtifact::Json] {
        eprintln!("targo trust: wrote {}", report_artifact_path(&output_root, artifact).display());
    }
    if unsafe_memory_report_artifact_path(&output_root).is_file() {
        eprintln!(
            "targo trust: wrote {}",
            unsafe_memory_report_artifact_path(&output_root).display()
        );
    }
    Ok(())
}

fn report_evidence_artifacts(
    report: &trust_types::JsonProofReport,
) -> Vec<&TransportEvidenceArtifact> {
    let mut artifacts = Vec::new();
    for function in &report.functions {
        for obligation in &function.obligations {
            if let Some(proof) = &obligation.proof_evidence {
                artifacts.extend(proof.artifacts.iter());
                if let Some(native) = &proof.native_trust_ir {
                    artifacts.extend(native.artifacts.iter());
                }
            }
            if let Some(transport) = &obligation.transport_evidence {
                if let Some(native) = &transport.native_trust_ir {
                    artifacts.extend(native.artifacts.iter());
                }
                if let Some(proof) = &transport.proof_evidence {
                    artifacts.extend(proof.artifacts.iter());
                }
            }
        }
    }
    artifacts
}

fn report_contains_path_materializations(report: &trust_types::JsonProofReport) -> bool {
    report_evidence_artifacts(report).into_iter().any(|artifact| {
        artifact
            .materialization
            .as_ref()
            .and_then(|materialization| materialization.materialized_path.as_deref())
            .is_some()
    })
}

fn inline_artifact_materializations(
    artifacts: &mut [TransportEvidenceArtifact],
    source_root: &Path,
    total_bytes: &mut u64,
) -> io::Result<()> {
    for artifact in artifacts {
        if artifact
            .materialization
            .as_ref()
            .and_then(|materialization| materialization.materialized_path.as_deref())
            .is_none()
        {
            continue;
        }
        let digest = artifact.digest.clone().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "path-backed report artifact has no declared digest",
            )
        })?;
        let bytes = artifact
            .materialization
            .as_ref()
            .expect("path-backed materialization checked")
            .decoded_bytes_at_root(&digest, source_root)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        *total_bytes = total_bytes.checked_add(bytes.len() as u64).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "inline report artifact byte overflow")
        })?;
        if *total_bytes > MAX_INLINE_REPORT_ARTIFACT_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "inline proof evidence exceeds the {MAX_INLINE_REPORT_ARTIFACT_BYTES}-byte aggregate limit; use --report-dir"
                ),
            ));
        }
        let materialization = artifact.materialization.as_mut().expect("materialization exists");
        materialization.encoding = "hex".to_string();
        materialization.byte_len = bytes.len() as u64;
        materialization.encoded_bytes = trust_types::digest::lowercase_hex(&bytes);
        materialization.materialized_path = None;
    }
    Ok(())
}

/// Re-inline one captured compiler run before its private artifact root is
/// dropped. Multi-run repair aggregation can then combine results from distinct
/// roots without retaining ambient path authority.
pub(crate) fn inline_verification_result_artifacts(
    results: &mut [VerificationResult],
    source_root: &Path,
) -> io::Result<()> {
    let source_root = source_root.canonicalize().map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("could not canonicalize captured proof artifact root: {error}"),
        )
    })?;
    let mut total_bytes = 0_u64;
    for result in results {
        let Some(mut evidence) = structured_transport_evidence(result) else {
            continue;
        };
        if let Some(native) = &mut evidence.native_trust_ir {
            inline_artifact_materializations(
                &mut native.artifacts,
                &source_root,
                &mut total_bytes,
            )?;
        }
        if let Some(proof) = &mut evidence.proof_evidence {
            inline_artifact_materializations(&mut proof.artifacts, &source_root, &mut total_bytes)?;
        }
        crate::types::replace_structured_transport_evidence(result, &evidence).map_err(
            |error| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("could not reserialize captured proof evidence: {error}"),
                )
            },
        )?;
    }
    Ok(())
}

/// Copy every referenced path-backed proof materialization into the report's
/// own canonical SHA-256 store. Saved reports then remain independently
/// verifiable after the compiler's private run store disappears, and diff/query
/// can resolve the same canonical relative descriptors beneath report_dir.
fn persist_report_artifact_store(
    report: &trust_types::JsonProofReport,
    source_root: Option<&Path>,
    output_dir: &Path,
) -> io::Result<()> {
    let path_backed = report_evidence_artifacts(report)
        .into_iter()
        .filter(|artifact| {
            artifact
                .materialization
                .as_ref()
                .and_then(|materialization| materialization.materialized_path.as_deref())
                .is_some()
        })
        .collect::<Vec<_>>();
    let output_root = preflight_report_output_root(output_dir)?;
    let source_root = source_root
        .map(|root| {
            let metadata = std::fs::symlink_metadata(root).map_err(|error| {
                io::Error::new(
                    error.kind(),
                    format!("could not inspect proof artifact source root: {error}"),
                )
            })?;
            if metadata.file_type().is_symlink() || !metadata.is_dir() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "proof artifact source root must be a non-symlink directory",
                ));
            }
            root.canonicalize().map_err(|error| {
                io::Error::new(
                    error.kind(),
                    format!("could not canonicalize proof artifact source root: {error}"),
                )
            })
        })
        .transpose()?;
    if source_root.as_ref().is_some_and(|root| !root.is_dir()) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "proof artifact source root is not a directory",
        ));
    }

    let destination_store =
        output_root.join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256");
    let output_owns_store = source_root.as_ref() != Some(&output_root);
    if output_owns_store {
        remove_path_if_exists(
            &output_root.join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY),
            "stale report proof artifact store",
        )?;
    }
    if path_backed.is_empty() {
        return Ok(());
    }
    let source_root = source_root.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "path-backed proof evidence has no explicit run artifact root",
        )
    })?;
    if output_owns_store {
        std::fs::create_dir_all(&destination_store)?;
    }

    let mut copied = BTreeSet::new();
    let mut total_bytes = 0_u64;
    for artifact in path_backed {
        let digest = artifact.digest.as_ref().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "path-backed report artifact has no declared digest",
            )
        })?;
        let materialization = artifact.materialization.as_ref().expect("filtered materialization");
        let first_copy = copied.insert(digest.value.clone());
        if first_copy {
            total_bytes = total_bytes.checked_add(materialization.byte_len).ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "report artifact byte count overflow")
            })?;
            if total_bytes > MAX_REPORT_ARTIFACT_STORE_BYTES {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "report proof artifact store exceeds the {MAX_REPORT_ARTIFACT_STORE_BYTES}-byte aggregate limit"
                    ),
                ));
            }
        }
        let bytes = materialization
            .decoded_bytes_at_root(digest, &source_root)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        if !first_copy || !output_owns_store {
            continue;
        }

        let destination = destination_store.join(&digest.value);
        let mut file =
            std::fs::OpenOptions::new().write(true).create_new(true).open(&destination).map_err(
                |error| {
                    io::Error::new(
                        error.kind(),
                        format!(
                            "could not create report proof artifact {}: {error}",
                            destination.display()
                        ),
                    )
                },
            )?;
        file.write_all(&bytes)?;
        file.sync_all()?;
    }

    Ok(())
}

fn write_unsafe_memory_report_wrapper(
    preflight: &UnsafeMemoryReportPreflight,
    output_dir: &Path,
) -> io::Result<()> {
    let proof_report_path = report_artifact_path(output_dir, ReportArtifact::Json);
    let proof_report_hash = file_sha256_hex(&proof_report_path)?;
    let wrapper = ProofUnsafeMemoryReport {
        schema: PROOF_UNSAFE_MEMORY_REPORT_SCHEMA,
        candidate_commit: preflight.candidate_commit.clone(),
        candidate_tree: preflight.candidate_tree.clone(),
        repo_dirty: false,
        producer: ProofUnsafeMemoryProducer { command: PROOF_UNSAFE_MEMORY_COMMAND, native: true },
        proof_report_path: ReportArtifact::Json.file_name(),
        proof_report_hash: format!("sha256:{proof_report_hash}"),
        coverage: preflight.coverage,
        unsupported: Vec::new(),
    };

    let wrapper_path = unsafe_memory_report_artifact_path(output_dir);
    let json = serde_json::to_vec_pretty(&wrapper).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("failed to serialize {PROOF_UNSAFE_MEMORY_REPORT_SCHEMA}: {error}"),
        )
    })?;
    std::fs::write(&wrapper_path, json).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!(
                "failed to write {PROOF_UNSAFE_MEMORY_REPORT_SCHEMA} at {}: {error}",
                wrapper_path.display()
            ),
        )
    })?;
    Ok(())
}

fn preflight_report_output_root(output_dir: &Path) -> io::Result<PathBuf> {
    match std::fs::symlink_metadata(output_dir) {
        Ok(metadata) => validate_report_output_root_metadata(&metadata)?,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            std::fs::create_dir_all(output_dir).map_err(|error| {
                io::Error::new(
                    error.kind(),
                    format!(
                        "failed to create report output root {}: {error}",
                        output_dir.display()
                    ),
                )
            })?;
            let metadata = std::fs::symlink_metadata(output_dir)?;
            validate_report_output_root_metadata(&metadata)?;
        }
        Err(error) => return Err(error),
    }
    output_dir.canonicalize().map_err(|error| {
        io::Error::new(error.kind(), format!("could not canonicalize report output root: {error}"))
    })
}

#[cfg(test)]
fn existing_report_output_root_is_safe(output_dir: &Path) -> io::Result<bool> {
    match std::fs::symlink_metadata(output_dir) {
        Ok(metadata) => {
            validate_report_output_root_metadata(&metadata)?;
            Ok(true)
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

fn validate_report_output_root_metadata(metadata: &std::fs::Metadata) -> io::Result<()> {
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "report output root must be a non-symlink directory",
        ));
    }
    Ok(())
}

fn sync_report_bundle(staged_root: &Path) -> io::Result<()> {
    for path in [
        report_artifact_path(staged_root, ReportArtifact::Ndjson),
        report_artifact_path(staged_root, ReportArtifact::Html),
        report_artifact_path(staged_root, ReportArtifact::Json),
        unsafe_memory_report_artifact_path(staged_root),
    ] {
        match std::fs::File::open(&path) {
            Ok(file) => file.sync_all()?,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    sync_directory(staged_root)
}

#[cfg(unix)]
fn sync_directory(path: &Path) -> io::Result<()> {
    std::fs::File::open(path)?.sync_all()
}

#[cfg(not(unix))]
fn sync_directory(_path: &Path) -> io::Result<()> {
    Ok(())
}

fn report_bundle_relative_paths() -> [PathBuf; 5] {
    [
        PathBuf::from(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY),
        PathBuf::from(ReportArtifact::Ndjson.file_name()),
        PathBuf::from(ReportArtifact::Html.file_name()),
        PathBuf::from(PROOF_UNSAFE_MEMORY_WRAPPER_FILE),
        // JSON is the bundle's commit marker and is installed last.
        PathBuf::from(ReportArtifact::Json.file_name()),
    ]
}

fn path_exists_without_following(path: &Path) -> io::Result<bool> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

fn restore_report_bundle_backups(
    output_root: &Path,
    backup_root: &Path,
    backed_up: &[PathBuf],
    installed: &[PathBuf],
) -> io::Result<()> {
    let mut failures = Vec::new();
    for relative in installed.iter().rev() {
        if let Err(error) = remove_path_if_exists(
            &output_root.join(relative),
            "partially installed report bundle artifact",
        ) {
            failures.push(error.to_string());
        }
    }
    for relative in backed_up.iter().rev() {
        if let Err(error) = std::fs::rename(backup_root.join(relative), output_root.join(relative))
        {
            failures.push(format!("could not restore {}: {error}", relative.display()));
        }
    }
    if failures.is_empty() {
        sync_directory(output_root)
    } else {
        Err(io::Error::other(format!(
            "could not roll back report bundle transaction: {}",
            failures.join("; ")
        )))
    }
}

fn commit_staged_report_bundle(staged_root: &Path, output_root: &Path) -> io::Result<()> {
    commit_staged_report_bundle_with_hook(staged_root, output_root, |_| Ok(()))
}

fn commit_staged_report_bundle_with_hook<F>(
    staged_root: &Path,
    output_root: &Path,
    mut before_install: F,
) -> io::Result<()>
where
    F: FnMut(&Path) -> io::Result<()>,
{
    let backup = tempfile::Builder::new()
        .prefix(".trust-report-backup-")
        .tempdir_in(output_root)
        .map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("could not create private report rollback directory: {error}"),
        )
    })?;
    let mut backed_up = Vec::new();
    for relative in report_bundle_relative_paths() {
        let destination = output_root.join(&relative);
        let exists = match path_exists_without_following(&destination) {
            Ok(exists) => exists,
            Err(error) => {
                let rollback =
                    restore_report_bundle_backups(output_root, backup.path(), &backed_up, &[]);
                return Err(io::Error::new(
                    error.kind(),
                    format!(
                        "could not inspect existing report artifact {}: {error}{}",
                        destination.display(),
                        rollback.err().map(|rollback| format!("; {rollback}")).unwrap_or_default()
                    ),
                ));
            }
        };
        if !exists {
            continue;
        }
        if let Err(error) = std::fs::rename(&destination, backup.path().join(&relative)) {
            let rollback =
                restore_report_bundle_backups(output_root, backup.path(), &backed_up, &[]);
            return Err(io::Error::new(
                error.kind(),
                format!(
                    "could not stage existing report artifact {} for rollback: {error}{}",
                    destination.display(),
                    rollback.err().map(|rollback| format!("; {rollback}")).unwrap_or_default()
                ),
            ));
        }
        backed_up.push(relative);
    }

    let mut installed = Vec::new();
    for relative in report_bundle_relative_paths() {
        let staged = staged_root.join(&relative);
        let exists = match path_exists_without_following(&staged) {
            Ok(exists) => exists,
            Err(error) => {
                let rollback = restore_report_bundle_backups(
                    output_root,
                    backup.path(),
                    &backed_up,
                    &installed,
                );
                return Err(io::Error::new(
                    error.kind(),
                    format!(
                        "could not inspect staged report artifact {}: {error}{}",
                        staged.display(),
                        rollback.err().map(|rollback| format!("; {rollback}")).unwrap_or_default()
                    ),
                ));
            }
        };
        if !exists {
            continue;
        }
        let destination = output_root.join(&relative);
        if let Err(error) = before_install(&relative) {
            let rollback =
                restore_report_bundle_backups(output_root, backup.path(), &backed_up, &installed);
            return Err(io::Error::new(
                error.kind(),
                format!(
                    "report bundle commit was interrupted before {}: {error}{}",
                    destination.display(),
                    rollback.err().map(|rollback| format!("; {rollback}")).unwrap_or_default()
                ),
            ));
        }
        if let Err(error) = std::fs::rename(&staged, &destination) {
            let rollback =
                restore_report_bundle_backups(output_root, backup.path(), &backed_up, &installed);
            return Err(io::Error::new(
                error.kind(),
                format!(
                    "could not commit staged report artifact {}: {error}{}",
                    destination.display(),
                    rollback.err().map(|rollback| format!("; {rollback}")).unwrap_or_default()
                ),
            ));
        }
        installed.push(relative);
    }
    if let Err(error) = sync_directory(output_root) {
        let rollback =
            restore_report_bundle_backups(output_root, backup.path(), &backed_up, &installed);
        return Err(io::Error::new(
            error.kind(),
            format!(
                "could not durably commit report bundle: {error}{}",
                rollback.err().map(|rollback| format!("; {rollback}")).unwrap_or_default()
            ),
        ));
    }
    Ok(())
}

/// Remove the previous committed report bundle before an evidence-grade test
/// run begins. If the child later fails before authenticated transport can be
/// parsed, consumers must observe no report rather than a stale successful
/// phase-B record from an earlier invocation.
pub(crate) fn invalidate_report_bundle(output_dir: &Path) -> io::Result<()> {
    let metadata = match std::fs::symlink_metadata(output_dir) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    validate_report_output_root_metadata(&metadata)?;
    for relative in report_bundle_relative_paths() {
        remove_path_if_exists(&output_dir.join(&relative), "previous report bundle artifact")?;
    }
    sync_directory(output_dir)
}

#[cfg(test)]
fn cleanup_report_artifacts(output_dir: &Path) -> io::Result<()> {
    if !existing_report_output_root_is_safe(output_dir)? {
        return Ok(());
    }

    for artifact in [ReportArtifact::Json, ReportArtifact::Ndjson, ReportArtifact::Html] {
        remove_report_artifact(output_dir, artifact)?;
    }

    Ok(())
}

#[cfg(test)]
fn cleanup_unsafe_memory_report_artifact(output_dir: &Path) -> io::Result<()> {
    if !existing_report_output_root_is_safe(output_dir)? {
        return Ok(());
    }
    remove_path_if_exists(&unsafe_memory_report_artifact_path(output_dir), "unsafe-memory report")
}

#[cfg(test)]
fn remove_report_artifact(output_dir: &Path, artifact: ReportArtifact) -> io::Result<()> {
    let artifact_path = report_artifact_path(output_dir, artifact);
    remove_path_if_exists(&artifact_path, artifact.write_label())
}

fn remove_path_if_exists(path: &Path, label: &str) -> io::Result<()> {
    let metadata = match std::fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    let result = if metadata.is_dir() && !metadata.file_type().is_symlink() {
        std::fs::remove_dir_all(path)
    } else {
        std::fs::remove_file(path)
    };
    match result {
        Ok(()) => {
            eprintln!("targo trust: removed stale {}", path.display());
            Ok(())
        }
        Err(error) => {
            let message = format!(
                "failed to remove stale {label} at {} before writing report artifacts: {error}",
                path.display()
            );
            eprintln!("targo trust: {message}");
            Err(io::Error::new(error.kind(), message))
        }
    }
}

fn unsafe_memory_report_artifact_path(output_dir: &Path) -> PathBuf {
    output_dir.join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE)
}

fn file_sha256_hex(path: &Path) -> io::Result<String> {
    trust_types::digest::stable_sha256_hex_reader(std::fs::File::open(path)?)
}

fn git_status_porcelain_lines(repo_root: &Path) -> io::Result<Vec<String>> {
    git_status_porcelain_lines_excluding(repo_root, None)
}

fn git_status_porcelain_lines_excluding(
    repo_root: &Path,
    excluded_relative_root: Option<&str>,
) -> io::Result<Vec<String>> {
    if excluded_relative_root.is_none() {
        return crate::controlled_git::exact_status_porcelain_v1(
            repo_root,
            "unsafe-memory report repository cleanliness probe",
            64 * 1024 * 1024,
            Duration::from_secs(30),
        )
        .map_err(io::Error::other);
    }
    crate::controlled_git::validate_status_authority(
        repo_root,
        "unsafe-memory report repository cleanliness probe",
        64 * 1024 * 1024,
        Duration::from_secs(30),
    )
    .map_err(io::Error::other)?;
    let excluded_pathspec =
        excluded_relative_root.map(|path| format!(":(top,literal,exclude){path}"));
    let mut args =
        vec!["status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none"];
    if let Some(excluded_pathspec) = excluded_pathspec.as_deref() {
        args.extend(["--", ".", excluded_pathspec]);
    }
    let stdout = crate::controlled_git::text_with_explicit_pathspec_magic(
        repo_root,
        &args,
        "unsafe-memory report repository cleanliness probe with output exclusion",
        64 * 1024 * 1024,
        Duration::from_secs(30),
    )
    .map_err(io::Error::other)?;
    let mut lines = if stdout.is_empty() {
        Vec::new()
    } else {
        stdout.lines().map(str::to_string).collect::<Vec<_>>()
    };
    if lines.iter().any(|line| line.len() < 3 || line.as_bytes()[2] != b' ') {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "controlled Git returned malformed porcelain-v1 status",
        ));
    }
    // Tracked porcelain rows are stat-based diagnostics. The fresh isolated
    // re-index below is authoritative for tracked mode/blob identity; retain
    // porcelain only for untracked paths outside the deliberate output root.
    lines.retain(|line| line.starts_with("?? "));
    if lines.is_empty() {
        lines = crate::controlled_git::tracked_content_status_porcelain_v1(
            repo_root,
            "unsafe-memory report content-authoritative cleanliness probe",
            excluded_relative_root,
            64 * 1024 * 1024,
            Duration::from_secs(30),
        )
        .map_err(io::Error::other)?;
    }
    if lines.is_empty() {
        crate::controlled_git::require_clean_submodules(
            repo_root,
            "unsafe-memory report recursive submodule cleanliness probe",
            64 * 1024 * 1024,
            Duration::from_secs(30),
        )
        .map_err(io::Error::other)?;
    }
    Ok(lines)
}

fn git_stdout(repo_root: &Path, args: &[&str]) -> io::Result<String> {
    crate::controlled_git::text(
        repo_root,
        args,
        &format!("report git {}", args.join(" ")),
        64 * 1024 * 1024,
        Duration::from_secs(30),
    )
    .map_err(io::Error::other)
}

fn is_full_git_sha(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}


#[cfg(test)]
mod tests {
    use std::fs;

    use trust_types::{
        TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX, TRUST_VC_PROOF_ARTIFACT_ID_PREFIX,
        TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX,
    };

    use super::*;
    use crate::types::transport_to_verification_result;

    fn result_with_location(location: Option<SourceSpan>) -> VerificationResult {
        VerificationResult {
            function: "crate::checked_add".into(),
            kind: "overflow:add".into(),
            message: "arithmetic overflow".into(),
            outcome: VerificationOutcome::Proved,
            backend: "ay-smtlib".into(),
            time_ms: Some(8),
            location,
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        }
    }

    fn full_verifier_result(outcome: VerificationOutcome) -> VerificationResult {
        VerificationResult {
            function: "crate::checked_contract".into(),
            kind: "unknown".into(),
            message: "unsupported MIR `FullVerification::Contract`: contract_id=requires:0".into(),
            outcome,
            backend: "trust-full-verifier".into(),
            time_ms: Some(0),
            location: Some(SourceSpan {
                file: "src/lib.rs".into(),
                line_start: 9,
                col_start: 1,
                line_end: 9,
                col_end: 12,
            }),
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        }
    }

    fn report_with_full_verifier_result(outcome: VerificationOutcome) -> VerificationReport {
        let result = full_verifier_result(outcome);
        report_with_result(result, outcome)
    }

    #[test]
    fn canonical_report_preserves_truthful_custom_package_lib_subject() {
        let target = crate::pipeline::transport::CargoTargetIdentity {
            package_id: "path+file:///workspace#custom-package@0.1.0".to_string(),
            package_name: "custom-package".to_string(),
            target_name: "custom-lib".to_string(),
            target_kinds: vec!["lib".to_string()],
            compile_target: "x86_64-unknown-linux-gnu".to_string(),
            compile_mode: "build".to_string(),
            compile_kind: "target".to_string(),
            unit_identity_sha256: "c".repeat(64),
            compile_target_spec_sha256: None,
            proof_unit_index: 0,
            proof_unit_mode: "test".to_string(),
            proof_unit_role: "primary".to_string(),
            semantics_sha256: "a".repeat(64),
        };
        let mut report = report_with_full_verifier_result(VerificationOutcome::Proved);
        report.report_subject = target.report_label();

        let canonical = report.to_trust_report();
        assert_eq!(canonical.crate_name, target.report_label());
        assert_ne!(canonical.crate_name, "crate");
    }

    fn report_with_result(
        result: VerificationResult,
        outcome: VerificationOutcome,
    ) -> VerificationReport {
        VerificationReport {
            report_subject: "test-report".to_string(),
            success: outcome.is_proved(),
            exit_code: if outcome.is_proved() { 0 } else { 1 },
            proved: usize::from(outcome.is_proved()),
            failed: usize::from(outcome.is_failed()),
            unknown: usize::from(outcome.is_inconclusive()),
            runtime_checked: usize::from(outcome.is_runtime_checked()),
            assumed: 0,
            mandated: 0,
            contract_panics: 0,
            cached: 0,
            total: 1,
            results: vec![result],
            zero_obligation_functions: Vec::new(),
            compiler_diagnostics: vec![CompilerDiagnostic {
                level: "note".into(),
                message: "native full verifier status: Proved; requested=1, proved=1, failed=0"
                    .into(),
            }],
            duration_ms: 11,
            config: ReportConfig {
                level: "L1".into(),
                timeout_ms: 5000,
                function_budget_ms: 120_000,
                enabled: true,
                hardened: false,
                trust_profile: None,
            },
            dep_assumptions: Vec::new(),
            gate: None,
            coverage: None,
            test_execution: None,
            cargo_proof_inventory: None,
            proof_artifact_root: None,
            live_transport_authority: None,
        }
    }

    #[test]
    fn canonical_report_preserves_live_monitor_evidence_but_scrubs_it_after_save() {
        let monitor = trust_types::TransportMonitorEvidence {
            status: trust_types::TransportMonitorStatus::Unmonitored,
            reason: "quantified propositions have no finite runtime monitor".into(),
            predicate_digest: format!("sha256:{}", "e".repeat(64)),
        };
        let transport = trust_types::TransportObligationResult {
            obligation_id: None,
            claim_digest_sha256: None,
            kind: "postcond".into(),
            typed_kind: Some(Box::new(VcKind::Postcondition)),
            description: "postcondition".into(),
            location: None,
            outcome: trust_types::Outcome::Unknown,
            solver: "trust-full-verifier".into(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: Some("static proof remains open".into()),
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: Some(monitor.clone()),
        };
        let result = transport_to_verification_result("crate::quantified", &transport);
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Unknown))
                .to_trust_report();
        let obligation = &report.functions[0].obligations[0];
        assert_eq!(obligation.kind, "postcondition");
        assert_eq!(obligation.proof_level, trust_types::ProofLevel::L1Functional);
        assert!(matches!(obligation.outcome, ObligationOutcome::Unknown { .. }));
        assert!(obligation.proof_evidence.is_none());
        assert_eq!(
            obligation.transport_evidence.as_ref().and_then(|evidence| evidence.monitor.clone()),
            Some(monitor.clone()),
        );

        let json = serde_json::to_string(&report).expect("serialize canonical report");
        let mut restored: trust_types::JsonProofReport =
            serde_json::from_str(&json).expect("deserialize canonical report");
        let _ = restored.sanitize_deserialized();
        assert!(
            restored.functions[0].obligations[0]
                .transport_evidence
                .as_ref()
                .and_then(|evidence| evidence.monitor.as_ref())
                .is_none(),
            "saved monitor evidence is diagnostic input, not a live authenticated monitor capability",
        );
    }

    fn report_with_results_and_diagnostics(
        results: Vec<VerificationResult>,
        compiler_diagnostics: Vec<CompilerDiagnostic>,
    ) -> VerificationReport {
        let (counts, _defects) = crate::pipeline::hardened::partition_outcome_counts(&results);
        let success = counts.failed == 0 && counts.unknown == 0 && counts.runtime_checked == 0;

        VerificationReport {
            report_subject: "test-report".to_string(),
            success,
            exit_code: if success { 0 } else { 1 },
            proved: counts.proved,
            failed: counts.failed,
            unknown: counts.unknown,
            runtime_checked: counts.runtime_checked,
            assumed: counts.assumed,
            mandated: counts.mandated,
            contract_panics: counts.contract_panics,
            cached: 0,
            total: counts.total,
            results,
            zero_obligation_functions: Vec::new(),
            compiler_diagnostics,
            duration_ms: 11,
            config: ReportConfig {
                level: "L1".into(),
                timeout_ms: 5000,
                function_budget_ms: 120_000,
                enabled: true,
                hardened: false,
                trust_profile: None,
            },
            dep_assumptions: Vec::new(),
            gate: None,
            coverage: None,
            test_execution: None,
            cargo_proof_inventory: None,
            proof_artifact_root: None,
            live_transport_authority: None,
        }
    }

    fn with_live_transport_authority(mut report: VerificationReport) -> VerificationReport {
        let authenticated_compiler_results = report.results.clone();
        report.zero_obligation_functions =
            crate::types::authenticated_zero_obligation_inventory(&authenticated_compiler_results);
        crate::types::normalize_authenticated_results_for_publication(
            &mut report.results,
            report.proof_artifact_root.as_deref(),
        );
        let (counts, _defects) =
            crate::pipeline::hardened::partition_outcome_counts(&report.results);
        report.total = counts.total;
        report.proved = counts.proved;
        report.failed = counts.failed;
        report.unknown = counts.unknown;
        report.runtime_checked = counts.runtime_checked;
        report.assumed = counts.assumed;
        report.mandated = counts.mandated;
        report.contract_panics = counts.contract_panics;
        let complete_zero_obligation_inventory = counts.total == 0
            && !report.zero_obligation_functions.is_empty()
            && report.coverage.as_ref().is_some_and(|coverage| {
                coverage.coverage_complete
                    && coverage.eligible == report.zero_obligation_functions.len()
                    && coverage.processed == coverage.eligible
            });
        let conditional = counts
            .assumed
            .saturating_add(counts.mandated)
            .saturating_add(counts.runtime_checked)
            .saturating_add(counts.contract_panics);
        let has_gate_failing_cargo_exclusions =
            cargo_has_gate_failing_exclusions(report.cargo_proof_inventory.as_ref());
        report.success = !has_gate_failing_cargo_exclusions
            && (complete_zero_obligation_inventory
                || (counts.total > 0
                    && counts.proved.saturating_add(conditional) == counts.total
                    && counts.failed + counts.unknown == 0));
        let decision = if report.success {
            if counts.assumed + counts.mandated + counts.runtime_checked + counts.contract_panics
                > 0
            {
                "conditional-pass"
            } else {
                "pass"
            }
        } else if counts.failed > 0 {
            "fail"
        } else {
            "inconclusive"
        };
        report.gate = Some(trust_types::VerificationGateReport {
            lane: "strict".into(),
            verification_level: Some(report.config.level.clone()),
            decision: decision.into(),
            exit_code: if report.success { 0 } else { 1 },
            counts: trust_types::VerificationGateCounts {
                total: counts.total,
                proved: counts.proved,
                failed: counts.failed,
                unknown: counts.unknown,
                runtime_checked: counts.runtime_checked,
                assumed: counts.assumed,
                mandated: counts.mandated,
                contract_panics: counts.contract_panics,
            },
            conditional_on_assumption_rows: counts.assumed > 0,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: counts.runtime_checked > 0,
            conditional_on_visitation_entries: false,
            coverage: report.coverage,
            test_execution: None,
        });
        report.live_transport_authority = LiveTransportAuthority::capture_authenticated_projection(
            &report.report_subject,
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
            &authenticated_compiler_results,
            &report.results,
            report.proof_artifact_root.as_deref(),
        );
        assert!(report.live_transport_authority.is_some(), "test live authority must be minted");
        assert!(report.seal_for_publication(), "test publication state must be sealed");
        report
    }

    #[test]
    fn write_report_artifacts_persists_json_ndjson_and_html() {
        let report = report_with_result(result_with_location(None), VerificationOutcome::Proved)
            .to_trust_report();
        let output_dir = tempfile::tempdir().expect("tempdir");

        write_report_artifacts(&report, output_dir.path(), "<html>trust</html>")
            .expect("report artifacts should be written");

        assert!(output_dir.path().join("report.json").is_file());
        assert!(output_dir.path().join("report.ndjson").is_file());
        assert!(output_dir.path().join("report.html").is_file());
        let persisted: trust_types::JsonProofReport = serde_json::from_slice(
            &fs::read(output_dir.path().join("report.json")).expect("read report.json"),
        )
        .expect("persisted report.json should deserialize");
        assert_eq!(persisted.metadata.timeout_ms, Some(5_000));
        assert_eq!(persisted.metadata.function_budget_ms, Some(120_000));
    }

    #[test]
    fn write_report_artifacts_fails_when_output_path_is_not_a_directory() {
        let report = report_with_result(result_with_location(None), VerificationOutcome::Proved)
            .to_trust_report();
        let temp = tempfile::tempdir().expect("tempdir");
        let output_path = temp.path().join("report-file");
        fs::write(&output_path, "not a directory").expect("write file in place of report dir");

        let err = write_report_artifacts(&report, &output_path, "<html>trust</html>")
            .expect_err("file path must reject report-dir artifact persistence");

        let message = err.to_string();
        assert!(message.contains("non-symlink"), "unexpected error message: {message}");
    }

    #[test]
    fn write_report_artifacts_replaces_stale_artifacts_before_commit_marker() {
        let report = report_with_result(result_with_location(None), VerificationOutcome::Proved)
            .to_trust_report();
        let output_dir = tempfile::tempdir().expect("tempdir");
        let stale_json = output_dir.path().join("report.json");
        let stale_html = output_dir.path().join("report.html");
        fs::write(&stale_json, r#"{"stale":true}"#).expect("write stale report json");
        fs::write(&stale_html, "<html>stale</html>").expect("write stale report html");
        fs::create_dir(output_dir.path().join("report.ndjson"))
            .expect("create stale directory at ndjson artifact path");

        write_report_artifacts(&report, output_dir.path(), "<html>trust</html>")
            .expect("stale artifact paths should be cleaned before writing reports");

        assert!(stale_json.is_file(), "fresh report.json commit marker should be written");
        assert!(output_dir.path().join("report.ndjson").is_file());
        assert_eq!(
            fs::read_to_string(stale_html).expect("read fresh html report"),
            "<html>trust</html>"
        );
        assert!(
            !fs::read_to_string(stale_json).expect("read fresh json report").contains("stale"),
            "stale report.json must be replaced before a successful artifact transaction"
        );
    }

    #[cfg(unix)]
    #[test]
    fn report_dir_symlink_is_rejected_without_deleting_target_artifacts() {
        use std::os::unix::fs::symlink;

        let report = report_with_result(result_with_location(None), VerificationOutcome::Proved)
            .to_trust_report();
        let temp = tempfile::tempdir().expect("tempdir");
        let target = temp.path().join("target");
        fs::create_dir(&target).expect("create symlink target");
        for name in
            ["report.json", "report.ndjson", "report.html", PROOF_UNSAFE_MEMORY_WRAPPER_FILE]
        {
            fs::write(target.join(name), format!("sentinel:{name}"))
                .expect("write target sentinel");
        }
        let link = temp.path().join("report-link");
        symlink(&target, &link).expect("create report-dir symlink");

        let error = write_report_artifacts(&report, &link, "<html>new</html>")
            .expect_err("symlinked report root must fail closed");
        assert!(error.to_string().contains("non-symlink"), "unexpected error: {error}");
        assert!(cleanup_report_artifacts(&link).is_err());
        assert!(cleanup_unsafe_memory_report_artifact(&link).is_err());
        for name in
            ["report.json", "report.ndjson", "report.html", PROOF_UNSAFE_MEMORY_WRAPPER_FILE]
        {
            assert_eq!(
                fs::read_to_string(target.join(name)).expect("read target sentinel"),
                format!("sentinel:{name}"),
                "rejected report-dir symlink modified its target"
            );
        }
    }

    #[test]
    fn path_backed_report_bundle_survives_removal_but_reload_loses_live_proof_authority() {
        let source = tempfile::tempdir().expect("source root");
        let (canonical, digest) = path_backed_canonical_report(source.path());
        let output = tempfile::tempdir().expect("report output");
        write_report_artifacts_from_root(
            &canonical,
            output.path(),
            "<html>trust</html>",
            Some(source.path()),
            None,
            None,
        )
        .expect("persist self-contained report bundle");
        let persisted_artifact = output
            .path()
            .join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY)
            .join("sha256")
            .join(&digest.value);
        assert!(persisted_artifact.is_file());

        drop(source);
        let loaded = crate::diff::load_report(&output.path().join("report.json"))
            .expect("rooted report reload should retain diagnostic evidence");
        assert_eq!(loaded.sanitization.downgraded_proved, 1);
        assert_eq!(loaded.sanitization.evidence_defects, 1);
        assert_eq!(loaded.untrusted_claims.obligations().len(), 1);
        assert_eq!(
            loaded.untrusted_claims.obligations()[0].outcome(),
            trust_types::UntrustedSavedOutcomeClaim::Proved
        );
        assert_eq!(loaded.report.summary.total_proved, 0);
        assert_eq!(loaded.report.summary.total_unknown, 1);
        assert_eq!(loaded.report.summary.verdict, trust_types::CrateVerdict::Inconclusive);
    }

    #[test]
    fn path_backed_stdout_requires_authority_and_reinlines_exact_bytes() {
        let source = tempfile::tempdir().expect("source root");
        let (report, _digest) = sealed_path_backed_native_report(source.path());
        assert!(report.proof_artifact_root.is_none(), "seal must consume mutable path authority");
        let canonical_before_removal = report.to_trust_report();
        assert!(!report_contains_path_materializations(&canonical_before_removal));

        drop(source);
        report
            .render(OutputFormat::Json, None)
            .expect("sealed inline bytes must survive removal of their former source root");
        let canonical_after_removal = report.to_trust_report();
        assert_eq!(
            serde_json::to_vec(&canonical_before_removal).unwrap(),
            serde_json::to_vec(&canonical_after_removal).unwrap(),
            "rendering after source removal must reuse the exact retained projection"
        );
    }

    #[test]
    fn report_transaction_removes_stale_store_only_after_success() {
        let source = tempfile::tempdir().expect("source root");
        let (path_report, _digest) = path_backed_canonical_report(source.path());
        let output = tempfile::tempdir().expect("report output");
        write_report_artifacts_from_root(
            &path_report,
            output.path(),
            "<html>path-backed</html>",
            Some(source.path()),
            None,
            None,
        )
        .expect("write path-backed report");
        let store = output.path().join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY);
        assert!(store.is_dir());

        let inline = report_with_result(result_with_location(None), VerificationOutcome::Proved)
            .to_trust_report();
        write_report_artifacts(&inline, output.path(), "<html>inline</html>")
            .expect("replace with inline-only report");
        assert!(!store.exists(), "stale report CAS survived an inline-only commit");
    }

    #[test]
    fn report_staging_failure_preserves_last_known_good_bundle() {
        let old = report_with_result(result_with_location(None), VerificationOutcome::Proved)
            .to_trust_report();
        let output = tempfile::tempdir().expect("report output");
        write_report_artifacts(&old, output.path(), "<html>old</html>").expect("write old report");
        let stale_store = output.path().join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY);
        fs::create_dir(&stale_store).expect("create old store");
        fs::write(stale_store.join("sentinel"), "old-store").expect("write old store sentinel");
        let old_json = fs::read(output.path().join("report.json")).expect("read old JSON");
        let old_html = fs::read(output.path().join("report.html")).expect("read old HTML");
        let old_ndjson = fs::read(output.path().join("report.ndjson")).expect("read old NDJSON");

        let source = tempfile::tempdir().expect("source root");
        let (new_report, digest) = path_backed_canonical_report(source.path());
        fs::remove_file(
            source
                .path()
                .join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY)
                .join("sha256")
                .join(digest.value),
        )
        .expect("remove new source artifact");
        write_report_artifacts_from_root(
            &new_report,
            output.path(),
            "<html>new</html>",
            Some(source.path()),
            None,
            None,
        )
        .expect_err("missing source artifact must abort before commit");

        assert_eq!(fs::read(output.path().join("report.json")).unwrap(), old_json);
        assert_eq!(fs::read(output.path().join("report.html")).unwrap(), old_html);
        assert_eq!(fs::read(output.path().join("report.ndjson")).unwrap(), old_ndjson);
        assert_eq!(fs::read_to_string(stale_store.join("sentinel")).unwrap(), "old-store");
        assert!(
            fs::read_dir(output.path()).expect("read output root").all(|entry| !entry
                .expect("output entry")
                .file_name()
                .to_string_lossy()
                .starts_with(".trust-report-stage-")),
            "failed staging left a partial report directory"
        );
    }

    #[test]
    fn report_commit_failure_rolls_back_partially_installed_bundle() {
        let output = tempfile::tempdir().expect("report output");
        let old_store = output.path().join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY);
        fs::create_dir(&old_store).expect("create old store");
        fs::write(old_store.join("old"), "old-store").expect("write old store");
        for (name, bytes) in [
            ("report.ndjson", "old-ndjson"),
            ("report.html", "old-html"),
            ("report.json", "old-json"),
            (PROOF_UNSAFE_MEMORY_WRAPPER_FILE, "old-wrapper"),
        ] {
            fs::write(output.path().join(name), bytes).expect("write old bundle fixture");
        }

        let staged = tempfile::Builder::new()
            .prefix(".trust-report-test-stage-")
            .tempdir_in(output.path())
            .expect("create staged bundle");
        let new_store = staged.path().join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY);
        fs::create_dir(&new_store).expect("create new store");
        fs::write(new_store.join("new"), "new-store").expect("write new store");
        for (name, bytes) in [
            ("report.ndjson", "new-ndjson"),
            ("report.html", "new-html"),
            ("report.json", "new-json"),
            (PROOF_UNSAFE_MEMORY_WRAPPER_FILE, "new-wrapper"),
        ] {
            fs::write(staged.path().join(name), bytes).expect("write staged bundle fixture");
        }

        let error =
            commit_staged_report_bundle_with_hook(staged.path(), output.path(), |relative| {
                if relative == Path::new("report.html") {
                    Err(io::Error::other("injected commit interruption"))
                } else {
                    Ok(())
                }
            })
            .expect_err("partial commit must roll back");
        assert!(error.to_string().contains("injected commit interruption"));
        assert_eq!(fs::read_to_string(old_store.join("old")).unwrap(), "old-store");
        assert!(!old_store.join("new").exists());
        for (name, bytes) in [
            ("report.ndjson", "old-ndjson"),
            ("report.html", "old-html"),
            ("report.json", "old-json"),
            (PROOF_UNSAFE_MEMORY_WRAPPER_FILE, "old-wrapper"),
        ] {
            assert_eq!(fs::read_to_string(output.path().join(name)).unwrap(), bytes);
        }
    }

    #[test]
    fn certified_test_start_invalidates_every_previous_committed_report_artifact() {
        let output = tempfile::tempdir().expect("report output");
        let store = output.path().join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY);
        fs::create_dir(&store).expect("create old artifact store");
        fs::write(store.join("old"), "old-store").expect("write old artifact");
        for name in
            ["report.ndjson", "report.html", "report.json", PROOF_UNSAFE_MEMORY_WRAPPER_FILE]
        {
            fs::write(output.path().join(name), "stale-success").expect("write stale report");
        }
        fs::write(output.path().join("unrelated.txt"), "preserve").expect("write unrelated file");

        invalidate_report_bundle(output.path()).expect("invalidate stale report bundle");

        for relative in report_bundle_relative_paths() {
            assert!(
                !output.path().join(&relative).exists(),
                "stale report artifact survived: {}",
                relative.display()
            );
        }
        assert_eq!(fs::read_to_string(output.path().join("unrelated.txt")).unwrap(), "preserve");
    }

    #[test]
    fn report_artifacts_render_propagates_write_failure() {
        let report = with_live_transport_authority(report_with_result(
            result_with_location(None),
            VerificationOutcome::Proved,
        ));
        let temp = tempfile::tempdir().expect("tempdir");
        let output_path = temp.path().join("report-file");
        fs::write(&output_path, "not a directory").expect("write file in place of report dir");

        let err = report
            .render(OutputFormat::Json, Some(output_path.to_str().expect("utf-8 temp path")))
            .expect_err(
                "render must fail closed when requested report artifacts cannot be written",
            );

        assert!(err.to_string().contains("non-symlink"), "unexpected error: {err}");
    }

    #[test]
    fn unsafe_memory_wrapper_binds_publishable_full_verifier_report() {
        let repo = clean_git_repo("unsafe-memory-wrapper-clean");
        let output_dir = repo.join("reports").join("proof");
        let request = UnsafeMemoryReportRequest::new(repo.clone());
        let report = with_live_transport_authority(report_with_result(
            trust_vc_native_transport_result(),
            VerificationOutcome::Proved,
        ));

        report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(output_dir.to_str().expect("utf-8 report dir")),
                Some(&request),
            )
            .expect("publishable unsafe-memory evidence should emit wrapper");

        let wrapper_path = output_dir.join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE);
        let wrapper: serde_json::Value =
            serde_json::from_slice(&fs::read(&wrapper_path).expect("read wrapper"))
                .expect("wrapper JSON");
        assert_eq!(wrapper["schema"], PROOF_UNSAFE_MEMORY_REPORT_SCHEMA);
        assert_eq!(wrapper["repo_dirty"], false);
        assert_eq!(wrapper["producer"]["command"], PROOF_UNSAFE_MEMORY_COMMAND);
        assert_eq!(wrapper["producer"]["native"], true);
        assert_eq!(wrapper["proof_report_path"], "report.json");
        assert_eq!(
            wrapper["proof_report_hash"],
            format!(
                "sha256:{}",
                file_sha256_hex(&output_dir.join("report.json")).expect("hash report")
            )
        );
        assert_eq!(wrapper["coverage"]["unsafe_blocks_total"], 1);
        assert_eq!(wrapper["coverage"]["unsafe_blocks_proved"], 1);
        assert_eq!(wrapper["coverage"]["unsafe_operations_total"], 1);
        assert_eq!(wrapper["coverage"]["unsafe_operations_proved"], 1);
        assert_eq!(wrapper["coverage"]["memory_obligations_total"], 1);
        assert_eq!(wrapper["coverage"]["memory_obligations_proved"], 1);
        assert!(wrapper["unsupported"].as_array().is_some_and(Vec::is_empty));

        let _ = fs::remove_dir_all(repo);
    }

    #[test]
    fn unsafe_memory_wrapper_rejects_dirty_repo() {
        let repo = clean_git_repo("unsafe-memory-wrapper-dirty");
        fs::write(repo.join("dirty.rs"), "unsafe fn dirty() {}\n").expect("write dirty file");
        let output_dir = repo.join("reports").join("proof");
        let request = UnsafeMemoryReportRequest::new(repo.clone());
        let report = with_live_transport_authority(report_with_result(
            trust_vc_native_transport_result(),
            VerificationOutcome::Proved,
        ));

        let error = report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(output_dir.to_str().expect("utf-8 report dir")),
                Some(&request),
            )
            .expect_err("dirty repo must reject unsafe-memory wrapper emission");

        assert!(error.to_string().contains("repo must be clean"), "{error}");
        assert!(!output_dir.join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE).exists());

        let _ = fs::remove_dir_all(repo);
    }

    #[test]
    fn unsafe_memory_wrapper_rejects_non_publishable_or_manual_evidence() {
        let repo = clean_git_repo("unsafe-memory-wrapper-rejects");
        let request = UnsafeMemoryReportRequest::new(repo.clone());

        let text_only_report = with_live_transport_authority(report_with_result(
            VerificationResult {
                kind: "unsafe_memory".into(),
                message: "unsafe memory proof row with no structured evidence".into(),
                ..full_verifier_result(VerificationOutcome::Proved)
            },
            VerificationOutcome::Proved,
        ));
        let text_error = text_only_report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(repo.join("reports/text").to_str().expect("utf-8 report dir")),
                Some(&request),
            )
            .expect_err("text-only unsafe-memory rows must not emit wrapper");
        assert!(
            text_error.to_string().contains("lacks publishable structured native proof evidence"),
            "{text_error}"
        );

        let mut manual = trust_vc_native_transport_result();
        manual.backend = "manual-stub-verifier".into();
        let manual_report =
            with_live_transport_authority(report_with_result(manual, VerificationOutcome::Proved));
        let manual_error = manual_report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(repo.join("reports/manual").to_str().expect("utf-8 report dir")),
                Some(&request),
            )
            .expect_err("manual/stub markers must reject wrapper emission");
        assert!(manual_error.to_string().contains("manual/stub/demo"), "{manual_error}");

        let _ = fs::remove_dir_all(repo);
    }

    fn sha256_digest(value: &str) -> trust_types::TransportArtifactDigest {
        assert_eq!(value.len(), 64);
        assert!(value.bytes().all(|byte| byte.is_ascii_hexdigit()));
        assert!(value.bytes().all(|byte| !byte.is_ascii_uppercase()));
        trust_types::TransportArtifactDigest { algorithm: "sha256".into(), value: value.into() }
    }

    fn trust_ir_stable_digest(value: &str) -> trust_types::TransportArtifactDigest {
        assert_eq!(value.len(), 64);
        assert!(value.bytes().all(|byte| byte.is_ascii_hexdigit()));
        assert!(value.bytes().all(|byte| !byte.is_ascii_uppercase()));
        trust_types::TransportArtifactDigest {
            algorithm: "trust_ir-stable-v1".into(),
            value: value.into(),
        }
    }

    fn native_trust_ir_shape_artifacts(
        suite: &str,
        request_id: &str,
        proof_id: &str,
    ) -> Vec<trust_types::TransportEvidenceArtifact> {
        let native_id = format!("trust_ir-native-{suite}-request-{request_id}-proof-{proof_id}");
        let bundle = native_test_materialization(
            "bundle",
            None,
            None,
            None,
            serde_json::json!({"bundle": "exact"}),
            &native_id,
            vec![],
        );
        let bundle_digest = bundle.1.value.clone();
        let bundle_uri = format!("trust_ir-native://verification-bundle/{bundle_digest}");
        let request = native_test_materialization(
            "request",
            Some(suite),
            Some(request_id),
            None,
            serde_json::json!({"request": "exact"}),
            &native_id,
            vec![trust_types::TransportArtifactReference {
                kind: "EngineInput".into(),
                digest: bundle.1.clone(),
            }],
        );
        let request_digest = request.1.value.clone();
        let normalized = native_test_materialization(
            "normalized_obligation",
            Some(suite),
            Some(request_id),
            Some(proof_id),
            serde_json::json!({"obligation": "exact"}),
            &native_id,
            vec![trust_types::TransportArtifactReference {
                kind: "EngineInput".into(),
                digest: request.1.clone(),
            }],
        );
        vec![
            native_test_artifact("EngineInput", bundle, bundle_uri.clone()),
            native_test_artifact(
                "EngineInput",
                request,
                format!("{bundle_uri}/{suite}/request/{request_id}/{request_digest}"),
            ),
            native_test_artifact(
                "NormalizedObligation",
                normalized.clone(),
                format!(
                    "{bundle_uri}/{suite}/request/{request_id}/{request_digest}/proof/{proof_id}/{}",
                    normalized.1.value
                ),
            ),
        ]
    }

    fn native_test_materialization(
        role: &str,
        suite: Option<&str>,
        request_id: Option<&str>,
        proof_id: Option<&str>,
        payload: serde_json::Value,
        native_id: &str,
        references: Vec<trust_types::TransportArtifactReference>,
    ) -> (trust_types::TransportArtifactMaterialization, trust_types::TransportArtifactDigest) {
        let mut value = serde_json::json!({
            "schema": trust_types::NATIVE_TRUST_IR_MATERIALIZATION_SCHEMA,
            "role": role,
            "suite": suite,
            "request_id": request_id,
            "proof_id": proof_id,
            "payload": payload,
        });
        canonicalize_test_json(&mut value);
        let bytes = serde_json::to_vec(&value).expect("serialize native materialization");
        let digest = trust_types::TransportArtifactDigest {
            algorithm: "sha256".into(),
            value: format!("{:x}", Sha256::digest(&bytes)),
        };
        (
            trust_types::TransportArtifactMaterialization::from_exact_bytes(
                &bytes, native_id, references,
            )
            .expect("native materialization"),
            digest,
        )
    }

    fn native_test_artifact(
        kind: &str,
        materialized: (
            trust_types::TransportArtifactMaterialization,
            trust_types::TransportArtifactDigest,
        ),
        uri: String,
    ) -> trust_types::TransportEvidenceArtifact {
        trust_types::TransportEvidenceArtifact {
            kind: kind.into(),
            format: Some("trust_ir-json".into()),
            artifact_id: None,
            digest: Some(materialized.1),
            uri: Some(uri),
            materialization: Some(materialized.0),
            metadata: None,
        }
    }

    fn canonicalize_test_json(value: &mut serde_json::Value) {
        match value {
            serde_json::Value::Array(values) => {
                for value in values {
                    canonicalize_test_json(value);
                }
            }
            serde_json::Value::Object(object) => {
                let old = std::mem::take(object);
                let mut entries = old.into_iter().collect::<Vec<_>>();
                entries.sort_by(|left, right| left.0.cmp(&right.0));
                for (key, mut value) in entries {
                    canonicalize_test_json(&mut value);
                    object.insert(key, value);
                }
            }
            _ => {}
        }
    }

    fn bound_test_artifact(
        kind: &str,
        payload: &[u8],
        binding: &str,
        owner: &str,
        mut references: Vec<trust_types::TransportArtifactReference>,
    ) -> trust_types::TransportEvidenceArtifact {
        const MAGIC: &[u8] = b"trust.evidence-artifact-binding-envelope.v1\0";
        references.sort();
        let mut bytes = MAGIC.to_vec();
        let push = |bytes: &mut Vec<u8>, value: &[u8]| {
            bytes.extend_from_slice(&(value.len() as u32).to_be_bytes());
            bytes.extend_from_slice(value);
        };
        push(&mut bytes, kind.as_bytes());
        push(&mut bytes, owner.as_bytes());
        push(&mut bytes, binding.as_bytes());
        bytes.extend_from_slice(&(references.len() as u32).to_be_bytes());
        for reference in &references {
            push(&mut bytes, reference.kind.as_bytes());
            push(&mut bytes, reference.digest.algorithm.as_bytes());
            push(&mut bytes, reference.digest.value.as_bytes());
        }
        bytes.extend_from_slice(&(payload.len() as u64).to_be_bytes());
        bytes.extend_from_slice(payload);
        let digest = format!("{:x}", Sha256::digest(&bytes));
        trust_types::TransportEvidenceArtifact {
            kind: kind.into(),
            format: Some("binary".into()),
            artifact_id: Some(kind.into()),
            digest: Some(sha256_digest(&digest)),
            uri: Some(format!("artifact://test/{kind}/{digest}")),
            materialization: Some(
                trust_types::TransportArtifactMaterialization::from_exact_bytes(
                    &bytes, binding, references,
                )
                .expect("bound test materialization"),
            ),
            metadata: None,
        }
    }

    fn externalize_test_artifact(
        root: &Path,
        artifact: &mut trust_types::TransportEvidenceArtifact,
    ) {
        let digest = artifact.digest.clone().expect("artifact digest");
        let materialization = artifact.materialization.take().expect("artifact materialization");
        let bytes = materialization.decoded_bytes().expect("decode materialization");
        let store = root.join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256");
        fs::create_dir_all(&store).expect("create test artifact store");
        fs::write(store.join(&digest.value), bytes).expect("persist test artifact");
        artifact.materialization = Some(
            materialization
                .with_materialized_path(format!(
                    "{}/sha256/{}",
                    trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY,
                    digest.value
                ))
                .expect("path materialization"),
        );
    }

    fn path_backed_native_report(
        source_root: &Path,
    ) -> (VerificationReport, trust_types::TransportArtifactDigest) {
        let mut transport = trust_vc_certificate_only_transport(
            format!("{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{}", "seed.json"),
            "seed",
        );
        let certificate = transport
            .proof_evidence
            .as_mut()
            .and_then(|proof| proof.artifacts.first_mut())
            .expect("certificate artifact");
        let digest = certificate.digest.clone().expect("certificate digest");
        externalize_test_artifact(source_root, certificate);
        let result = transport_to_verification_result("crate::trust_vc_memory_owner", &transport);
        let mut report = report_with_result(result, VerificationOutcome::Proved);
        report.proof_artifact_root =
            Some(source_root.canonicalize().expect("canonical test proof artifact source root"));
        (report, digest)
    }

    fn sealed_path_backed_native_report(
        source_root: &Path,
    ) -> (VerificationReport, trust_types::TransportArtifactDigest) {
        let (report, digest) = path_backed_native_report(source_root);
        (with_live_transport_authority(report), digest)
    }

    /// Forge an observational, path-backed DTO solely to exercise the saved
    /// report bundle transaction. Production canonical publication never uses
    /// this route: its live seal inlines the bytes before exposing a report.
    fn path_backed_canonical_report(
        source_root: &Path,
    ) -> (trust_types::JsonProofReport, trust_types::TransportArtifactDigest) {
        let (report, digest) = path_backed_native_report(source_root);
        let evidence = structured_transport_evidence(&report.results[0])
            .expect("path-backed structured transport evidence");
        let mut canonical = report.to_trust_report();
        let obligation = &mut canonical.functions[0].obligations[0];
        let strength = ProofStrength::smt_unsat();
        obligation.outcome = ObligationOutcome::Proved { strength: strength.clone() };
        obligation.evidence = Some(ProofEvidence::from(strength));
        obligation.transport_evidence = Some(trust_types::ObligationTransportEvidenceReport {
            obligation_id: evidence.obligation_id,
            claim_digest_sha256: evidence.claim_digest_sha256,
            typed_kind: evidence.typed_kind,
            native_trust_ir: evidence.native_trust_ir,
            proof_evidence: evidence.proof_evidence,
            monitor: evidence.monitor,
        });
        canonical.recompute_summaries_from_obligation_outcomes();
        (canonical, digest)
    }

    fn clean_git_repo(prefix: &str) -> PathBuf {
        let tempdir = tempfile::Builder::new().prefix(prefix).tempdir().expect("temp git repo");
        let repo = tempdir.path().to_path_buf();
        std::mem::forget(tempdir);
        run_git(&repo, &["init"]);
        run_git(&repo, &["config", "user.email", "trust-tests@example.invalid"]);
        run_git(&repo, &["config", "user.name", "Trust Tests"]);
        fs::write(repo.join("README.md"), "fixture\n").expect("write fixture file");
        run_git(&repo, &["add", "."]);
        run_git(&repo, &["commit", "-m", "fixture"]);
        repo
    }

    fn run_git(repo: &Path, args: &[&str]) {
        let output = Command::new("git")
            .arg("-C")
            .arg(repo)
            .args(args)
            .output()
            .unwrap_or_else(|error| panic!("run git {}: {error}", args.join(" ")));
        assert!(
            output.status.success(),
            "git {} failed\nstdout:\n{}\nstderr:\n{}",
            args.join(" "),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn native_full_verifier_transport() -> trust_types::TransportObligationResult {
        let owner = "trust_ir-native-trust-wp-request-7-proof-42";
        let native_id = "trust_ir-native-trust-wp-request-7-proof-42";
        let input = bound_test_artifact(
            "NormalizedObligation",
            b"exact normalized trust-wp obligation",
            native_id,
            owner,
            vec![],
        );
        let transcript = bound_test_artifact(
            "SolverTranscript",
            b"exact trust-wp solver transcript",
            native_id,
            owner,
            vec![trust_types::TransportArtifactReference {
                kind: input.kind.clone(),
                digest: input.digest.clone().expect("input digest"),
            }],
        );
        let check = bound_test_artifact(
            "ProofCheckReport",
            b"exact trust-wp proof-check report",
            native_id,
            owner,
            vec![trust_types::TransportArtifactReference {
                kind: transcript.kind.clone(),
                digest: transcript.digest.clone().expect("transcript digest"),
            }],
        );
        trust_types::TransportObligationResult {
            obligation_id: Some(owner.into()),
            claim_digest_sha256: Some(
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into(),
            ),
            kind: "postcond".into(),
            typed_kind: Some(Box::new(VcKind::Postcondition)),
            description: "postcondition".into(),
            location: Some(SourceSpan {
                file: "src/lib.rs".into(),
                line_start: 9,
                col_start: 1,
                line_end: 9,
                col_end: 12,
            }),
            outcome: trust_types::Outcome::Proved,
            solver: "trust-wp".into(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: Some("native full verifier status: Proved".into()),
            design_mandate: false,
            native_trust_ir: Some(trust_types::TransportNativeTrustIrEvidence {
                suite: "trust-wp".into(),
                backend: "trust-wp".into(),
                request_id: Some("7".into()),
                native_id: Some("trust_ir-native-trust-wp-request-7-proof-42".into()),
                present: true,
                artifacts: native_trust_ir_shape_artifacts("trust-wp", "7", "42"),
                diagnostics: vec![trust_types::TransportEvidenceDiagnostic {
                    code: "native_trust_ir.accepted".into(),
                    severity: trust_types::TransportEvidenceDiagnosticSeverity::Info,
                    message: "typed TrustIr native request accepted".into(),
                    detail: Some("suite=trust-wp request_id=7 proof_obligation_id=42".into()),
                }],
            }),
            proof_evidence: Some(trust_types::TransportProofEvidence {
                suite: "trust-wp".into(),
                backend: "trust-wp".into(),
                request_id: Some("7".into()),
                proof_id: Some("42".into()),
                native_id: Some("trust_ir-native-trust-wp-request-7-proof-42".into()),
                status: trust_types::TransportProofStatus::Proved,
                strength: Some(ProofStrength::deductive()),
                evidence: Some(trust_types::ProofEvidence::from(ProofStrength::deductive())),
                artifacts: vec![input, transcript, check],
                diagnostics: vec![trust_types::TransportEvidenceDiagnostic {
                    code: "suite.accepted".into(),
                    severity: trust_types::TransportEvidenceDiagnosticSeverity::Info,
                    message: "trust-wp suite produced accepted proof evidence".into(),
                    detail: Some("primary owner trust-wp@7".into()),
                }],
            }),
            monitor: None,
        }
    }

    fn native_full_verifier_transport_result() -> VerificationResult {
        let transport = native_full_verifier_transport();
        transport_to_verification_result("crate::checked_contract", &transport)
    }

    fn clean_cic_hardened_transport() -> trust_types::TransportObligationResult {
        // Exact held payload bytes, matching the compiler's v2 publication
        // shape: the outer proof and its sole artifact are both addressed by
        // the framed digest of this serialized metadata value.
        let payload = serde_json::to_value(trust_ir::ProofEvidence::CleanCic {
            term: vec![1, 2, 3, 5, 8],
            context: vec![13, 21],
            lineage: trust_ir::ProofDigest::sha256([0xab; 32]),
            kernel_recheck: None,
        })
        .expect("serialize typed CleanCic test payload");
        let bytes = serde_json::to_vec(&payload).expect("serialize CleanCic test payload");
        let digest = trustc_domain_length_bound_sha256_hex("trustc.transport-clean-cic.v2", &bytes);
        let proof_id = format!("clean-cic:v2:{digest}");
        let strength = ProofStrength {
            reasoning: trust_types::ReasoningKind::Constructive,
            assurance: trust_types::AssuranceLevel::Certified,
        };

        trust_types::TransportObligationResult {
            obligation_id: Some("crate::paths::render:hardened-cleancic".into()),
            claim_digest_sha256: Some(
                "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".into(),
            ),
            kind: "hardened_byte_loss".into(),
            typed_kind: None,
            description: "hardened boundary (byte_loss): Path::as_os_str: byte-exact rendering"
                .into(),
            location: Some(SourceSpan {
                file: "src/path.rs".into(),
                line_start: 23,
                col_start: 9,
                line_end: 23,
                col_end: 32,
            }),
            outcome: trust_types::Outcome::Proved,
            solver: "clean-kernel".into(),
            time_ms: 1,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: Some(trust_types::TransportProofEvidence {
                suite: "trust-certify".into(),
                backend: "clean-kernel".into(),
                request_id: None,
                proof_id: Some(proof_id.clone()),
                native_id: None,
                status: TransportProofStatus::Proved,
                strength: Some(strength.clone()),
                evidence: Some(trust_types::ProofEvidence::from(strength)),
                artifacts: vec![trust_types::TransportEvidenceArtifact {
                    kind: "clean_cic".into(),
                    format: Some("trust-ir-cleancic-v2".into()),
                    artifact_id: Some(proof_id),
                    digest: Some(trust_types::TransportArtifactDigest {
                        algorithm: "sha256".into(),
                        value: digest.clone(),
                    }),
                    uri: Some(format!("trust-certify://clean-cic/{digest}")),
                    materialization: None,
                    metadata: Some(payload),
                }],
                diagnostics: Vec::new(),
            }),
            monitor: None,
        }
    }

    fn clean_cic_hardened_result() -> VerificationResult {
        let transport = clean_cic_hardened_transport();
        transport_to_verification_result("crate::paths::render", &transport)
    }

    fn promoted_proof_evidence_for_transport(
        transport: trust_types::TransportObligationResult,
    ) -> Option<ObligationProofEvidenceReport> {
        let result = transport_to_verification_result("crate::checked_contract", &transport);
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let trust_report = report.to_trust_report();
        trust_report.functions[0].obligations[0].proof_evidence.clone()
    }

    fn trust_vc_native_transport_result() -> VerificationResult {
        let seed_digest = "6666666666666666666666666666666666666666666666666666666666666666";
        let transport = trust_vc_certificate_only_transport(
            format!("{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{seed_digest}.json"),
            seed_digest,
        );
        transport_to_verification_result("crate::trust_vc_memory_owner", &transport)
    }

    fn native_transport_for_suite(suite: &str) -> trust_types::TransportObligationResult {
        let mut transport = native_full_verifier_transport();
        let native_id = format!("trust_ir-native-{suite}-request-7-proof-42");
        transport.obligation_id = Some(native_id.clone());
        transport.solver = suite.to_string();
        transport.reason = Some(format!("{suite} native proof status: Proved"));
        if let Some(native_trust_ir) = transport.native_trust_ir.as_mut() {
            native_trust_ir.suite = suite.into();
            native_trust_ir.backend = suite.into();
            native_trust_ir.native_id = Some(native_id.clone());
            native_trust_ir.artifacts = native_trust_ir_shape_artifacts(suite, "7", "42");
            native_trust_ir.diagnostics = vec![trust_types::TransportEvidenceDiagnostic {
                code: "native_trust_ir.accepted".into(),
                severity: trust_types::TransportEvidenceDiagnosticSeverity::Info,
                message: "typed TrustIr native request accepted".into(),
                detail: Some(format!("suite={suite} request_id=7 proof_obligation_id=42")),
            }];
        }
        if let Some(proof) = transport.proof_evidence.as_mut() {
            proof.suite = suite.into();
            proof.backend = suite.into();
            proof.native_id = Some(native_id.clone());
            proof.diagnostics = vec![trust_types::TransportEvidenceDiagnostic {
                code: "suite.accepted".into(),
                severity: trust_types::TransportEvidenceDiagnosticSeverity::Info,
                message: format!("{suite} suite produced accepted proof evidence"),
                detail: Some(format!("primary owner {suite}@7")),
            }];
            let input = bound_test_artifact(
                "NormalizedObligation",
                format!("exact normalized {suite} obligation").as_bytes(),
                &native_id,
                &native_id,
                vec![],
            );
            let transcript = bound_test_artifact(
                "SolverTranscript",
                format!("exact {suite} solver transcript").as_bytes(),
                &native_id,
                &native_id,
                vec![trust_types::TransportArtifactReference {
                    kind: input.kind.clone(),
                    digest: input.digest.clone().expect("input digest"),
                }],
            );
            let check = bound_test_artifact(
                "ProofCheckReport",
                format!("exact {suite} proof-check report").as_bytes(),
                &native_id,
                &native_id,
                vec![trust_types::TransportArtifactReference {
                    kind: transcript.kind.clone(),
                    digest: transcript.digest.clone().expect("transcript digest"),
                }],
            );
            proof.artifacts = vec![input, transcript, check];
        }
        transport
    }

    fn trust_vc_certificate_only_transport(
        certificate_uri: String,
        certificate_digest: &str,
    ) -> trust_types::TransportObligationResult {
        let mut transport = native_transport_for_suite("trust-vc");
        transport.obligation_id = Some("vc:trust_vc_memory_owner:memory_safety:0".into());
        // This fixture represents a proved first-class VC, so its compact tag,
        // exact typed identity, and adjacent description must remain one
        // coherent classification.  The obligation id may retain the
        // trust-vc memory-safety subject label; it is not the VC kind.
        transport.kind = VcKind::Postcondition.transport_tag();
        transport.typed_kind = Some(Box::new(VcKind::Postcondition));
        transport.description = VcKind::Postcondition.description();
        if let Some(native_trust_ir) = transport.native_trust_ir.as_mut() {
            native_trust_ir.request_id = Some("0".into());
            native_trust_ir.native_id = Some("trust_ir-native-trust-vc-request-0-proof-2".into());
            native_trust_ir.artifacts = native_trust_ir_shape_artifacts("trust-vc", "0", "2");
        }
        if let Some(proof) = transport.proof_evidence.as_mut() {
            proof.request_id = Some("0".into());
            proof.proof_id = Some("2".into());
            proof.native_id = Some("trust_ir-native-trust-vc-request-0-proof-2".into());
            let mut certificate = bound_test_artifact(
                "ProofCertificate",
                b"exact trust-vc replayable certificate",
                "trust_ir-native-trust-vc-request-0-proof-2",
                "vc:trust_vc_memory_owner:memory_safety:0",
                vec![],
            );
            let actual_digest =
                certificate.digest.as_ref().expect("certificate digest").value.clone();
            certificate.artifact_id =
                Some(format!("{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}{actual_digest}"));
            certificate.uri = Some(certificate_uri.replace(certificate_digest, &actual_digest));
            proof.artifacts = vec![certificate];
        }
        transport
    }

    fn hardened_transport_result_with_context() -> VerificationResult {
        let owner = "crate::paths::render:hardened0";
        let native_id = "trust_ir-native-trust-wp-request-8-proof-9";
        let input = bound_test_artifact(
            "NormalizedObligation",
            b"exact hardened normalized obligation",
            native_id,
            owner,
            vec![],
        );
        let transcript = bound_test_artifact(
            "SolverTranscript",
            b"exact hardened solver transcript",
            native_id,
            owner,
            vec![trust_types::TransportArtifactReference {
                kind: input.kind.clone(),
                digest: input.digest.clone().expect("input digest"),
            }],
        );
        let check = bound_test_artifact(
            "ProofCheckReport",
            b"exact hardened proof-check report",
            native_id,
            owner,
            vec![trust_types::TransportArtifactReference {
                kind: transcript.kind.clone(),
                digest: transcript.digest.clone().expect("transcript digest"),
            }],
        );
        let transport = trust_types::TransportObligationResult {
            obligation_id: Some(owner.into()),
            claim_digest_sha256: Some(
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
            ),
            kind: "hardened_byte_loss".into(),
            typed_kind: None,
            description: "hardened boundary (byte_loss): Path::as_os_str: byte-exact rendering"
                .into(),
            location: Some(SourceSpan {
                file: "src/path.rs".into(),
                line_start: 17,
                col_start: 9,
                line_end: 17,
                col_end: 32,
            }),
            outcome: trust_types::Outcome::Proved,
            solver: "trust-wp".into(),
            time_ms: 4,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: Some(trust_types::TransportNativeTrustIrEvidence {
                suite: "trust-wp".into(),
                backend: "trust-wp".into(),
                request_id: Some("8".into()),
                native_id: Some("trust_ir-native-trust-wp-request-8-proof-9".into()),
                present: true,
                artifacts: native_trust_ir_shape_artifacts("trust-wp", "8", "9"),
                diagnostics: vec![trust_types::TransportEvidenceDiagnostic {
                    code: "unix.model_assumption".into(),
                    severity: trust_types::TransportEvidenceDiagnosticSeverity::Info,
                    message: "model assumption: Unix OsStr preserves raw bytes at boundary".into(),
                    detail: Some("argv/env/path bytes remain byte-exact".into()),
                }],
            }),
            proof_evidence: Some(trust_types::TransportProofEvidence {
                suite: "trust-wp".into(),
                backend: "trust-wp".into(),
                request_id: Some("8".into()),
                proof_id: Some("9".into()),
                native_id: Some("trust_ir-native-trust-wp-request-8-proof-9".into()),
                status: TransportProofStatus::Proved,
                strength: Some(ProofStrength::deductive()),
                evidence: Some(trust_types::ProofEvidence::from(ProofStrength::deductive())),
                artifacts: vec![input, transcript, check],
                diagnostics: Vec::new(),
            }),
            monitor: None,
        };
        transport_to_verification_result("crate::paths::render", &transport)
    }

    #[test]
    fn terminal_result_line_includes_binary_location() {
        let result = result_with_location(Some(SourceSpan::binary_address(0x40105a)));

        assert_eq!(
            terminal_result_line(&result),
            "  [PROVED] [overflow:add] arithmetic overflow @ binary:0x40105a (ay-smtlib, 8ms)"
        );
    }

    #[test]
    fn terminal_result_line_includes_source_span_location() {
        let result = result_with_location(Some(SourceSpan {
            file: "src/lib.rs".into(),
            line_start: 7,
            col_start: 5,
            line_end: 7,
            col_end: 16,
        }));

        assert_eq!(
            terminal_result_line(&result),
            "  [PROVED] [overflow:add] arithmetic overflow @ src/lib.rs:7:5-16 (ay-smtlib, 8ms)"
        );
    }

    #[test]
    fn terminal_result_line_omits_empty_location() {
        let result = result_with_location(Some(SourceSpan::default()));

        assert_eq!(
            terminal_result_line(&result),
            "  [PROVED] [overflow:add] arithmetic overflow (ay-smtlib, 8ms)"
        );
    }

    #[test]
    fn trust_report_carries_native_full_verifier_proof_evidence() {
        let report = with_live_transport_authority(report_with_result(
            native_full_verifier_transport_result(),
            VerificationOutcome::Proved,
        ));
        let trust_report = report.to_trust_report();
        let obligation = &trust_report.functions[0].obligations[0];

        assert_eq!(
            obligation.obligation_id.as_deref(),
            Some("trust_ir-native-trust-wp-request-7-proof-42")
        );
        assert_eq!(obligation.solver, "trust-wp");
        assert_eq!(obligation.kind, "postcondition");
        assert_eq!(obligation.proof_level, trust_types::ProofLevel::L1Functional);
        assert_eq!(obligation.description, "postcondition");
        let evidence = obligation.proof_evidence.as_ref().expect("full verifier evidence");
        assert_eq!(evidence.suite.as_deref(), Some("trust-wp"));
        assert_eq!(evidence.backend, "trust-wp");
        assert_eq!(evidence.request_id.as_deref(), Some("7"));
        assert_eq!(evidence.proof_id.as_deref(), Some("42"));
        assert_eq!(
            evidence.native_id.as_deref(),
            Some("trust_ir-native-trust-wp-request-7-proof-42")
        );
        assert_eq!(evidence.status, Some(TransportProofStatus::Proved));
        assert_eq!(evidence.strength, ProofStrength::deductive());
        assert_eq!(evidence.artifacts.len(), 3);
        assert!(evidence.artifacts.iter().any(is_solver_transcript_artifact));
        assert!(evidence.artifacts.iter().any(is_replay_or_check_artifact));
        assert_eq!(evidence.diagnostics.len(), 1);
        assert_eq!(
            evidence.native_trust_ir.as_ref().and_then(|native| native.request_id.as_deref()),
            Some("7")
        );
        match &evidence.provenance {
            ObligationEvidenceProvenanceReport::NativeBackend { verifier } => {
                assert_eq!(verifier, "trust-wp");
            }
            other => panic!("unexpected provenance: {other:?}"),
        }
        let warnings = evidence.solver_warnings.as_ref().expect("solver warnings");
        assert!(
            warnings.iter().any(|warning| warning.contains("native full verifier status: Proved"))
        );
        assert!(warnings.iter().any(|warning| warning.contains("native_trust_ir.accepted")));
        assert!(warnings.iter().any(|warning| warning.contains("suite.accepted")));

        let json = serde_json::to_value(&trust_report).expect("serialize trust report");
        assert_eq!(
            json["functions"][0]["obligations"][0]["obligation_id"],
            "trust_ir-native-trust-wp-request-7-proof-42"
        );
        assert_eq!(
            json["functions"][0]["obligations"][0]["proof_evidence"]["strength"]["reasoning"],
            "Deductive"
        );
        assert_eq!(json["functions"][0]["obligations"][0]["proof_evidence"]["suite"], "trust-wp");
        assert_eq!(json["functions"][0]["obligations"][0]["proof_evidence"]["status"], "proved");
        assert_eq!(
            json["functions"][0]["obligations"][0]["proof_evidence"]["native_trust_ir"]["request_id"],
            "7"
        );
        assert!(
            json["functions"][0]["obligations"][0]["proof_evidence"]["artifacts"]
                .as_array()
                .is_some_and(|artifacts| !artifacts.is_empty())
        );
        assert!(
            json["functions"][0]["obligations"][0]["proof_evidence"]["solver_warnings"]
                .as_array()
                .expect("solver warnings")
                .iter()
                .any(|warning| warning
                    .as_str()
                    .is_some_and(|warning| warning.contains("native_trust_ir.accepted")))
        );
    }

    #[test]
    fn authenticated_untyped_lossy_native_proof_fails_closed() {
        let mut transport = native_full_verifier_transport();
        transport.kind = "unknown".into();
        transport.typed_kind = None;
        transport.description =
            "unsupported MIR `FullVerification::Contract`: contract_id=requires:0".into();
        transport.reason = None;

        let result = transport_to_verification_result("crate::checked_contract", &transport);
        assert_eq!(result.outcome, VerificationOutcome::Unknown);
        assert!(result.reason.as_deref().is_some_and(|reason| {
            reason.contains("omitted the exact typed VC kind")
                && reason.contains("downgraded before publication")
        }));

        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Unknown));
        assert_eq!(report.proved, 0);
        assert_eq!(report.unknown, 1);
        assert!(!report.success);

        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_proved, 0);
        assert_eq!(canonical.summary.total_unknown, 1);
        assert_eq!(canonical.summary.verdict, trust_types::CrateVerdict::Inconclusive);
        let obligation = &canonical.functions[0].obligations[0];
        assert_eq!(obligation.kind, "unsupported_mir");
        assert!(matches!(obligation.outcome, ObligationOutcome::Unknown { .. }));
        assert!(obligation.proof_evidence.is_none());
    }

    #[test]
    fn nested_hard_full_verifier_outcomes_survive_lossy_typed_kind_defects() {
        for (status, expected) in [
            (trust_types::TransportProofStatus::Failed, VerificationOutcome::Failed),
            (trust_types::TransportProofStatus::Timeout, VerificationOutcome::Timeout),
        ] {
            let mut transport = native_full_verifier_transport();
            transport.kind = "unknown".into();
            transport.typed_kind = None;
            transport.description =
                "unsupported MIR `FullVerification::Contract`: contract_id=requires:0".into();
            transport.outcome = trust_types::Outcome::Proved;
            transport.solver = "trust-full-verifier".into();
            transport.reason = None;
            transport.proof_evidence.as_mut().expect("proof evidence").status = status;

            let result = transport_to_verification_result("crate::checked_contract", &transport);
            assert_eq!(result.outcome, expected, "nested status {status:?}");
            assert!(
                result.reason.is_none(),
                "typed-kind diagnostics must not overwrite a nested hard outcome"
            );
        }
    }

    #[test]
    fn text_only_native_full_verifier_notes_do_not_become_proof_evidence() {
        let report = report_with_full_verifier_result(VerificationOutcome::Proved);
        let trust_report = report.to_trust_report();
        let obligation = &trust_report.functions[0].obligations[0];

        assert!(obligation.proof_evidence.is_none());
    }

    #[test]
    fn unknown_full_verifier_report_stays_inconclusive_not_runtime_checked() {
        let report = report_with_full_verifier_result(VerificationOutcome::Unknown);
        let trust_report = report.to_trust_report();

        assert_eq!(trust_report.summary.total_unknown, 1);
        assert_eq!(trust_report.summary.total_runtime_checked, 0);
        assert_eq!(trust_report.summary.verdict, trust_types::CrateVerdict::Inconclusive);
        assert_eq!(trust_report.functions[0].summary.unknown, 1);
        assert_eq!(trust_report.functions[0].summary.runtime_checked, 0);
        assert_eq!(
            trust_report.functions[0].summary.verdict,
            trust_types::FunctionVerdict::Inconclusive
        );
        match &trust_report.functions[0].obligations[0].outcome {
            ObligationOutcome::Unknown { reason } => {
                assert!(
                    reason.contains("native full verifier status")
                        || reason.contains("static proof"),
                    "{reason}"
                );
            }
            other => panic!("full-verifier unknown must stay unknown, got {other:?}"),
        }
    }

    #[test]
    fn sanitized_cached_replay_report_stays_unknown_without_proof_credit() {
        let transport = trust_types::TransportObligationResult {
            obligation_id: Some("obl-cache".into()),
            claim_digest_sha256: None,
            kind: "postcondition".into(),
            typed_kind: None,
            description: "cached proof row downgraded by compiler replay".into(),
            location: None,
            outcome: trust_types::Outcome::Unknown,
            solver: "trust-full-verifier".into(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: Some("cached proved row is non-evidentiary and was downgraded".into()),
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
        };
        let result = transport_to_verification_result("crate::cached_contract", &transport);
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Unknown));
        let trust_report = report.to_trust_report();
        let obligation = &trust_report.functions[0].obligations[0];

        assert_eq!(trust_report.summary.total_proved, 0);
        assert_eq!(trust_report.summary.total_unknown, 1);
        assert!(trust_report.summary.proof_grade_engine_statuses.is_empty());
        assert_eq!(obligation.obligation_id.as_deref(), Some("obl-cache"));
        assert!(obligation.proof_evidence.is_none());
        match &obligation.outcome {
            ObligationOutcome::Unknown { reason } => {
                assert!(reason.contains("non-evidentiary"));
            }
            other => panic!("cached replay row must stay unknown, got {other:?}"),
        }
    }

    #[test]
    fn thin_structured_native_full_verifier_notes_do_not_become_proof_evidence() {
        let mut transport = native_full_verifier_transport();
        transport.native_trust_ir = None;
        if let Some(proof) = transport.proof_evidence.as_mut() {
            proof.strength = None;
            proof.evidence = None;
            proof.artifacts.clear();
        }
        let result = transport_to_verification_result("crate::checked_contract", &transport);
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let trust_report = report.to_trust_report();
        let obligation = &trust_report.functions[0].obligations[0];

        assert!(obligation.proof_evidence.is_none());
    }

    #[test]
    fn publishable_native_proof_promotes_without_full_verifier_text() {
        let result = trust_vc_native_transport_result();
        assert!(!is_full_verifier_result(&result));

        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let trust_report = report.to_trust_report();
        let obligation = &trust_report.functions[0].obligations[0];

        assert_eq!(
            obligation.obligation_id.as_deref(),
            Some("vc:trust_vc_memory_owner:memory_safety:0")
        );
        assert!(obligation.transport_evidence.is_some());
        let evidence = obligation.proof_evidence.as_ref().expect("native proof evidence");
        assert_eq!(evidence.suite.as_deref(), Some("trust-vc"));
        assert_eq!(evidence.backend, "trust-vc");
        assert_eq!(evidence.request_id.as_deref(), Some("0"));
        assert_eq!(evidence.proof_id.as_deref(), Some("2"));
        assert_eq!(
            evidence.native_id.as_deref(),
            Some("trust_ir-native-trust-vc-request-0-proof-2")
        );
        assert_eq!(evidence.status, Some(TransportProofStatus::Proved));
        assert_eq!(evidence.strength, ProofStrength::deductive());
        assert_eq!(evidence.evidence, ProofEvidence::from(ProofStrength::deductive()));
        assert!(!evidence.artifacts.is_empty());
        assert_eq!(
            evidence.native_trust_ir.as_ref().and_then(|native| native.request_id.as_deref()),
            Some("0")
        );
    }

    #[test]
    fn synthetic_publishable_evidence_has_no_authority_without_live_compiler_receipt() {
        let result = trust_vc_native_transport_result();
        assert!(compiler_claim_digest(&result).is_some());
        let report = report_with_result(result, VerificationOutcome::Proved);

        let canonical = report.to_trust_report();
        let obligation = &canonical.functions[0].obligations[0];
        assert_eq!(canonical.summary.total_proved, 0);
        assert_eq!(canonical.summary.total_unknown, 1);
        assert!(matches!(obligation.outcome, ObligationOutcome::Unknown { .. }));
        assert!(obligation.proof_evidence.is_none());
        assert!(obligation.transport_evidence.is_none());
    }

    #[test]
    fn live_compiler_receipt_rejects_row_mutation_reordering_and_evidence_donation() {
        let first = trust_vc_native_transport_result();
        let mut second_transport = native_full_verifier_transport();
        second_transport.claim_digest_sha256 =
            Some("dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd".into());
        let second = transport_to_verification_result("crate::second_contract", &second_transport);
        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![first, second],
            Vec::new(),
        ));
        assert_eq!(report.to_trust_report().summary.total_proved, 2);

        let assert_rejected = |mutated: VerificationReport, label: &str| {
            let canonical = mutated.to_trust_report();
            assert_eq!(canonical.summary.total_proved, 0, "{label}");
            assert_eq!(canonical.summary.total_unknown, 2, "{label}");
            assert!(
                canonical.functions.iter().all(|function| function
                    .obligations
                    .iter()
                    .all(|obligation| obligation.proof_evidence.is_none())),
                "{label}"
            );
        };

        let mut reordered = report.clone();
        reordered.results.swap(0, 1);
        assert_rejected(reordered, "row reorder");

        let mut function_mutated = report.clone();
        function_mutated.results[0].function.push_str("::forged");
        assert_rejected(function_mutated, "function mutation");

        for (label, mutate) in [
            ("claim digest mutation", 0usize),
            ("obligation id donation", 1usize),
            ("native identity mutation", 2usize),
            ("artifact digest mutation", 3usize),
        ] {
            let mut mutated = report.clone();
            let mut evidence =
                structured_transport_evidence(&mutated.results[0]).expect("structured evidence");
            match mutate {
                0 => evidence.claim_digest_sha256 = Some("e".repeat(64)),
                1 => evidence.obligation_id = Some("donated-obligation".into()),
                2 => {
                    evidence.native_trust_ir.as_mut().expect("native evidence").native_id =
                        Some("donated-native-id".into());
                }
                3 => {
                    evidence.proof_evidence.as_mut().expect("proof evidence").artifacts[0]
                        .digest
                        .as_mut()
                        .expect("artifact digest")
                        .value = "f".repeat(64);
                }
                _ => unreachable!(),
            }
            crate::types::replace_structured_transport_evidence(&mut mutated.results[0], &evidence)
                .expect("replace structured evidence");
            assert_rejected(mutated, label);
        }
    }

    #[test]
    fn final_publication_seal_rejects_run_policy_and_completeness_mutations() {
        let report = with_live_transport_authority(report_with_result(
            trust_vc_native_transport_result(),
            VerificationOutcome::Proved,
        ));
        assert_eq!(report.to_trust_report().summary.total_proved, 1);

        let assert_rejected = |mutated: VerificationReport, label: &str| {
            let canonical = mutated.to_trust_report();
            assert_eq!(canonical.summary.total_proved, 0, "{label}");
            assert_eq!(canonical.summary.total_unknown, 1, "{label}");
            assert_eq!(
                canonical.summary.verdict,
                trust_types::CrateVerdict::Inconclusive,
                "{label}"
            );
            assert!(
                canonical.hardened.as_ref().is_none_or(|context| context
                    .boundary_inventory
                    .iter()
                    .all(|entry| entry.role != HardenedBoundaryInventoryRole::ProofEvidence)),
                "{label}"
            );
        };

        let mut config = report.clone();
        config.config.timeout_ms += 1;
        assert_rejected(config, "config mutation");

        let mut coverage = report.clone();
        coverage.coverage = Some(trust_types::VerificationCoverage::from_counts(1, 1));
        assert_rejected(coverage, "coverage mutation");

        let mut success = report.clone();
        success.success = false;
        assert_rejected(success, "success mutation");

        let mut zero_inventory = report.clone();
        zero_inventory.zero_obligation_functions.push("crate::forged_empty".into());
        assert_rejected(zero_inventory, "zero-obligation inventory mutation");

        let mut gate = report;
        gate.gate.as_mut().expect("sealed gate").lane = "forged-lane".into();
        assert_rejected(gate, "gate mutation");
    }

    #[test]
    fn live_focused_query_accepts_genuine_proof_but_serialized_copy_loses_authority() {
        let report = with_live_transport_authority(report_with_result(
            trust_vc_native_transport_result(),
            VerificationOutcome::Proved,
        ));
        let capability = report
            .sealed_canonical_report()
            .expect("sealed live report should mint the opaque query capability");
        assert_eq!(
            crate::report_query::run_live_focused_check_query(
                &capability,
                "crate::trust_vc_memory_owner",
                OutputFormat::Terminal,
            ),
            0,
            "genuine Proved may satisfy a focused query only while live publication authority exists"
        );

        let live = report.to_trust_report();
        assert_eq!(live.summary.total_proved, 1);

        let bytes = serde_json::to_vec(&live).expect("serialize live report");
        let restored: trust_types::JsonProofReport =
            serde_json::from_slice(&bytes).expect("deserialize saved report");
        assert_eq!(restored.summary.total_proved, 0);
        assert_eq!(restored.summary.total_unknown, 1);
        assert_eq!(restored.summary.verdict, trust_types::CrateVerdict::Inconclusive);
    }

    #[test]
    fn exclusion_free_cargo_inventory_is_sealed_and_preserves_live_authority() {
        let unit = trust_types::CargoProofUnitReport {
            package_id: "path+file:///workspace#root@0.1.0".into(),
            package_name: "root".into(),
            target_name: "root".into(),
            target_kinds: vec!["lib".into()],
            compile_target: "x86_64-unknown-linux-gnu".into(),
            compile_target_spec_sha256: None,
            proof_unit_index: 0,
            proof_unit_mode: "test".into(),
            proof_unit_role: "primary".into(),
            graph_role: "primary".into(),
            exclusion_reason: None,
            semantics_sha256: None,
            semantics: None,
        };
        let inventory = trust_types::CargoProofInventoryReport {
            schema: trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V1.into(),
            include_dependencies: true,
            declared: trust_types::CargoProofUnitPartitions {
                primary_roots: vec![unit.clone()],
                test_execution_units: Vec::new(),
                dependency_units: Vec::new(),
            },
            completed: trust_types::CargoProofUnitPartitions {
                primary_roots: vec![unit.clone()],
                test_execution_units: Vec::new(),
                dependency_units: Vec::new(),
            },
            covered: trust_types::CargoProofUnitPartitions {
                primary_roots: vec![unit],
                test_execution_units: Vec::new(),
                dependency_units: Vec::new(),
            },
            excluded_active_units: Vec::new(),
        };
        let mut report =
            report_with_result(trust_vc_native_transport_result(), VerificationOutcome::Proved);
        report.cargo_proof_inventory = Some(inventory.clone());
        let report = with_live_transport_authority(report);

        let canonical = report.to_trust_report();
        assert_eq!(canonical.cargo_proof_inventory, Some(inventory.clone()));
        let serialized = serde_json::to_vec(&canonical).expect("serialize canonical report");
        let restored: trust_types::JsonProofReport =
            serde_json::from_slice(&serialized).expect("deserialize saved report");
        assert_eq!(restored.cargo_proof_inventory, Some(inventory));
        assert_eq!(restored.summary.total_proved, 0);

        let mut mutated = report;
        mutated.cargo_proof_inventory.as_mut().expect("inventory retained").include_dependencies =
            false;
        assert!(
            mutated.sealed_canonical_report().is_err(),
            "post-seal observational inventory mutation must invalidate the complete report receipt"
        );
    }

    #[test]
    fn active_cargo_exclusions_cap_verdict_gate_and_live_proof_consumption() {
        use crate::pipeline::transport::{
            TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
            TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED,
            TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST, TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY,
            TARGO_TRUST_EXCLUSION_DOCUMENTATION,
        };

        let primary = trust_types::CargoProofUnitReport {
            package_id: "path+file:///workspace#root@0.1.0".into(),
            package_name: "root".into(),
            target_name: "root".into(),
            target_kinds: vec!["lib".into()],
            compile_target: "x86_64-unknown-linux-gnu".into(),
            compile_target_spec_sha256: None,
            proof_unit_index: 0,
            proof_unit_mode: "build".into(),
            proof_unit_role: "primary".into(),
            graph_role: "primary".into(),
            exclusion_reason: None,
            semantics_sha256: None,
            semantics: None,
        };
        let excluded = [
            (
                1,
                "run-custom-build",
                "control",
                "build-script-build",
                vec!["custom-build"],
                TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
            ),
            (2, "doctest", "primary", "root", vec!["lib"], TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST),
            (3, "doc", "primary", "root-doc", vec!["lib"], TARGO_TRUST_EXCLUSION_DOCUMENTATION),
            (
                4,
                "build",
                "dependency",
                "policy-dep",
                vec!["lib"],
                TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY,
            ),
            (
                5,
                "build",
                "dependency",
                "compile-time-filtered",
                vec!["lib"],
                TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED,
            ),
        ]
        .into_iter()
        .map(|(index, mode, graph_role, target_name, target_kinds, reason)| {
            trust_types::CargoProofUnitReport {
                package_id: format!("registry+https://example.invalid#index#unit-{index}@1.0.0"),
                package_name: format!("unit-{index}"),
                target_name: target_name.into(),
                target_kinds: target_kinds.into_iter().map(str::to_string).collect(),
                compile_target: "x86_64-unknown-linux-gnu".into(),
                compile_target_spec_sha256: None,
                proof_unit_index: index,
                proof_unit_mode: mode.into(),
                proof_unit_role: "excluded".into(),
                graph_role: graph_role.into(),
                exclusion_reason: Some(reason.into()),
                semantics_sha256: None,
                semantics: None,
            }
        })
        .collect::<Vec<_>>();
        let inventory = trust_types::CargoProofInventoryReport {
            schema: trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V1.into(),
            include_dependencies: false,
            declared: trust_types::CargoProofUnitPartitions {
                primary_roots: vec![primary.clone()],
                test_execution_units: Vec::new(),
                dependency_units: Vec::new(),
            },
            completed: trust_types::CargoProofUnitPartitions {
                primary_roots: vec![primary.clone()],
                test_execution_units: Vec::new(),
                dependency_units: Vec::new(),
            },
            covered: trust_types::CargoProofUnitPartitions {
                primary_roots: vec![primary],
                test_execution_units: Vec::new(),
                dependency_units: Vec::new(),
            },
            excluded_active_units: excluded,
        };
        let mut report =
            report_with_result(trust_vc_native_transport_result(), VerificationOutcome::Proved);
        report.cargo_proof_inventory = Some(inventory);
        let report = with_live_transport_authority(report);

        assert!(!report.success, "an excluded active Unit must cap the run gate");
        let gate = report.gate.as_ref().expect("gate");
        assert_eq!(gate.decision, "inconclusive");
        assert_eq!(gate.exit_code, 1);

        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.verdict, trust_types::CrateVerdict::Inconclusive);
        assert_eq!(canonical.summary.total_proved, 1, "proved rows remain useful evidence");
        let labels = cargo_active_exclusion_labels(canonical.cargo_proof_inventory.as_ref());
        assert_eq!(labels.len(), 5);
        for reason in [
            TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
            TARGO_TRUST_EXCLUSION_DEFERRED_DOCTEST,
            TARGO_TRUST_EXCLUSION_DOCUMENTATION,
            TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY,
            TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED,
        ] {
            assert!(
                labels.iter().any(|label| label.contains(reason)),
                "missing {reason}: {labels:?}"
            );
        }
        let terminal = report.terminal_lines().join("\n");
        assert!(terminal.contains("Cargo proof scope: INCOMPLETE — 5 active Unit(s)"));
        assert!(terminal.contains("package_id="));
        assert!(terminal.contains("compile_target_spec_sha256="));
        assert!(terminal.contains("proof_role=\"excluded\""));
        assert!(terminal.contains("graph_role="));
        assert!(terminal.contains(TARGO_TRUST_EXCLUSION_COMPILE_TIME_DEPS_FILTERED));

        let error = report
            .sealed_canonical_report()
            .err()
            .expect("active exclusions must withhold the live proof capability")
            .to_string();
        assert!(error.contains("exclusion-free Cargo proof frontier"), "{error}");
        assert!(error.contains("5 active Cargo Unit(s)"), "{error}");
        assert!(error.contains(TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION), "{error}");
    }

    #[test]
    fn dep_tcb_admitted_exclusions_do_not_cap_the_crate_gate() {
        // A frontier whose ONLY exclusions are ledger-admitted third-party
        // dependency libraries (dependency-policy) and a build-script control
        // job must still reach a passing gate at 0 unknown / 0 failed: those
        // Units are trusted-assumed (recorded as Conditional assumptions), not
        // proof gaps. This is the ny-cert four-zeros case.
        use crate::pipeline::transport::{
            TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION, TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY,
        };
        let primary = trust_types::CargoProofUnitReport {
            package_id: "path+file:///workspace#root@0.1.0".into(),
            package_name: "root".into(),
            target_name: "root".into(),
            target_kinds: vec!["lib".into()],
            compile_target: "x86_64-unknown-linux-gnu".into(),
            compile_target_spec_sha256: None,
            proof_unit_index: 0,
            proof_unit_mode: "build".into(),
            proof_unit_role: "primary".into(),
            graph_role: "primary".into(),
            exclusion_reason: None,
            semantics_sha256: None,
            semantics: None,
        };
        let excluded = [
            (
                1,
                "build",
                "dependency",
                "serde",
                vec!["lib"],
                TARGO_TRUST_EXCLUSION_DEPENDENCY_POLICY,
            ),
            (
                2,
                "run-custom-build",
                "control",
                "build-script-build",
                vec!["custom-build"],
                TARGO_TRUST_EXCLUSION_BUILD_SCRIPT_EXECUTION,
            ),
        ]
        .into_iter()
        .map(|(index, mode, graph_role, target_name, target_kinds, reason)| {
            trust_types::CargoProofUnitReport {
                package_id: format!("registry+https://example.invalid#index#unit-{index}@1.0.0"),
                package_name: format!("unit-{index}"),
                target_name: target_name.into(),
                target_kinds: target_kinds.into_iter().map(str::to_string).collect(),
                compile_target: "x86_64-unknown-linux-gnu".into(),
                compile_target_spec_sha256: None,
                proof_unit_index: index,
                proof_unit_mode: mode.into(),
                proof_unit_role: "excluded".into(),
                graph_role: graph_role.into(),
                exclusion_reason: Some(reason.into()),
                semantics_sha256: None,
                semantics: None,
            }
        })
        .collect::<Vec<_>>();
        let inventory = trust_types::CargoProofInventoryReport {
            schema: trust_types::CARGO_PROOF_INVENTORY_REPORT_SCHEMA_V1.into(),
            include_dependencies: false,
            declared: trust_types::CargoProofUnitPartitions {
                primary_roots: vec![primary.clone()],
                test_execution_units: Vec::new(),
                dependency_units: Vec::new(),
            },
            completed: trust_types::CargoProofUnitPartitions {
                primary_roots: vec![primary.clone()],
                test_execution_units: Vec::new(),
                dependency_units: Vec::new(),
            },
            covered: trust_types::CargoProofUnitPartitions {
                primary_roots: vec![primary],
                test_execution_units: Vec::new(),
                dependency_units: Vec::new(),
            },
            excluded_active_units: excluded,
        };
        // Every excluded Unit is admitted, so nothing fails the gate ...
        assert!(cargo_gate_failing_exclusion_labels(Some(&inventory)).is_empty());
        assert!(!cargo_has_gate_failing_exclusions(Some(&inventory)));
        // ... yet both remain fully visible as active exclusions for the ledger.
        assert_eq!(cargo_active_exclusion_labels(Some(&inventory)).len(), 2);

        let mut report =
            report_with_result(trust_vc_native_transport_result(), VerificationOutcome::Proved);
        report.cargo_proof_inventory = Some(inventory);
        let report = with_live_transport_authority(report);

        assert!(report.success, "admitted-only exclusions must not cap the gate");
        let gate = report.gate.as_ref().expect("gate");
        assert!(
            matches!(gate.decision.as_str(), "pass" | "conditional-pass"),
            "unexpected gate decision {:?}",
            gate.decision
        );
        assert_eq!(gate.exit_code, 0);

        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.verdict, trust_types::CrateVerdict::Verified);
        assert_eq!(canonical.summary.total_proved, 1);
        // The two admitted Units are still fully recorded (dep-TCB ledger
        // admission is covered directly by `dep_tcb::tests`); here we assert the
        // gate-level consequence only.

        // The live proof capability is still withheld while any Unit sits
        // outside the frontier — that stricter gate is intentionally unchanged.
        assert!(report.sealed_canonical_report().is_err());
    }

    #[test]
    fn trust_vc_native_trust_ir_certificate_promotes_without_solver_transcript() {
        let digest = "6666666666666666666666666666666666666666666666666666666666666666";
        let transport = trust_vc_certificate_only_transport(
            format!("{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{digest}.json"),
            digest,
        );

        let evidence = promoted_proof_evidence_for_transport(transport)
            .expect("trust-vc certificate evidence");

        assert_eq!(evidence.suite.as_deref(), Some("trust-vc"));
        assert_eq!(evidence.artifacts.len(), 1);
        assert!(evidence.artifacts.iter().any(is_trust_vc_digest_bound_proof_certificate_artifact));
        assert!(!evidence.artifacts.iter().any(is_solver_transcript_artifact));
    }

    #[test]
    fn trust_vc_native_trust_ir_certificate_ignores_unmaterialized_legacy_descriptor() {
        let certificate_digest = "4a73c5e6c2a0bc07feab9af4e3274d7dc9709b4a087e62208f37beba0836a066";
        let mut transport = trust_vc_certificate_only_transport(
            format!(
                "{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{certificate_digest}.json"
            ),
            certificate_digest,
        );
        if let Some(proof) = transport.proof_evidence.as_mut() {
            proof.artifacts.push(trust_types::TransportEvidenceArtifact {
                kind: "NormalizedObligation".into(),
                format: None,
                artifact_id: None,
                digest: Some(trust_ir_stable_digest(
                    "d953c07d22f10bea35a4e9520dc55b42e11afb1a4eedcb0791099b49d377ee3e",
                )),
                uri: Some(
                    "trust_ir-native://verification-bundle/a230ca36b5dde7ad2c9e802e57d4f4987115efc511b7f2c975fd966151c8abe2/trust-vc/request/0/proof/2"
                        .into(),
                ),
                materialization: None,
                metadata: None,
            });
        }

        let evidence = promoted_proof_evidence_for_transport(transport)
            .expect("valid certificate remains load-bearing");
        assert!(evidence.artifacts.iter().any(|artifact| {
            artifact.digest.as_ref().is_some_and(|digest| digest.algorithm == "trust_ir-stable-v1")
                && artifact.materialization.is_none()
        }));
    }

    #[test]
    fn trust_vc_exported_certificate_promotes_without_solver_transcript() {
        let digest = "7777777777777777777777777777777777777777777777777777777777777777";
        let transport = trust_vc_certificate_only_transport(
            format!(
                "{TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX}{TRUST_VC_PROOF_ARTIFACT_ID_PREFIX}{digest}.alethe"
            ),
            digest,
        );

        let evidence = promoted_proof_evidence_for_transport(transport)
            .expect("trust-vc exported certificate");

        assert_eq!(evidence.suite.as_deref(), Some("trust-vc"));
        assert_eq!(evidence.artifacts.len(), 1);
        assert!(evidence.artifacts.iter().any(is_trust_vc_digest_bound_proof_certificate_artifact));
        assert!(!evidence.artifacts.iter().any(is_solver_transcript_artifact));
    }

    #[test]
    fn trust_vc_certificate_uri_must_match_digest_for_promotion() {
        let digest = "8888888888888888888888888888888888888888888888888888888888888888";
        let mismatched_digest = "9999999999999999999999999999999999999999999999999999999999999999";
        let transport = trust_vc_certificate_only_transport(
            format!(
                "{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{mismatched_digest}.json"
            ),
            digest,
        );

        assert!(promoted_proof_evidence_for_transport(transport).is_none());
    }

    #[test]
    fn publishable_native_proof_requires_matching_native_ids() {
        let mut transport = native_full_verifier_transport();
        if let Some(proof) = transport.proof_evidence.as_mut() {
            proof.native_id = Some("different-native-id".into());
        }
        let result = transport_to_verification_result("crate::checked_contract", &transport);
        let report = report_with_result(result, VerificationOutcome::Proved);
        let trust_report = report.to_trust_report();
        let obligation = &trust_report.functions[0].obligations[0];

        assert!(obligation.proof_evidence.is_none());
        assert!(obligation.transport_evidence.is_none());
    }

    #[test]
    fn report_restores_proved_only_for_exact_publication_grade_row() {
        fn rendered_obligation(
            transport: trust_types::TransportObligationResult,
        ) -> trust_types::ObligationReport {
            let result = transport_to_verification_result("crate::checked_contract", &transport);
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved))
                .to_trust_report()
                .functions
                .remove(0)
                .obligations
                .remove(0)
        }

        let transport = native_full_verifier_transport();
        let valid = rendered_obligation(transport);
        assert!(matches!(valid.outcome, ObligationOutcome::Proved { .. }));
        assert!(valid.proof_evidence.is_some());

        let mut wrong_owner = native_full_verifier_transport();
        wrong_owner.obligation_id = Some("different-obligation".into());
        let wrong_owner = rendered_obligation(wrong_owner);
        assert!(matches!(wrong_owner.outcome, ObligationOutcome::Unknown { .. }));
        assert!(wrong_owner.proof_evidence.is_none());

        let mut incomplete_dag = native_full_verifier_transport();
        incomplete_dag
            .proof_evidence
            .as_mut()
            .expect("proof evidence")
            .artifacts
            .retain(|artifact| !is_replay_or_check_artifact(artifact));
        let incomplete_dag = rendered_obligation(incomplete_dag);
        assert!(matches!(incomplete_dag.outcome, ObligationOutcome::Unknown { .. }));
        assert!(incomplete_dag.proof_evidence.is_none());
    }

    #[test]
    fn publishable_native_proof_requires_matching_backend_and_native_artifact_shape() {
        let mut backend_splice = native_full_verifier_transport();
        backend_splice.native_trust_ir.as_mut().expect("native evidence").backend =
            "attacker-backend".into();
        assert!(promoted_proof_evidence_for_transport(backend_splice).is_none());

        let mut wrong_kind = native_full_verifier_transport();
        wrong_kind.native_trust_ir.as_mut().expect("native evidence").artifacts[2].kind =
            "banana".into();
        assert!(promoted_proof_evidence_for_transport(wrong_kind).is_none());

        let mut wrong_uri = native_full_verifier_transport();
        wrong_uri.native_trust_ir.as_mut().expect("native evidence").artifacts[1].uri =
            Some("artifact://attacker/request/7".into());
        assert!(promoted_proof_evidence_for_transport(wrong_uri).is_none());
    }

    #[test]
    fn publishable_native_proof_rejects_bounded_and_unchecked_strength() {
        let mut bounded = native_full_verifier_transport();
        if let Some(proof) = bounded.proof_evidence.as_mut() {
            proof.strength = Some(ProofStrength::bounded(32));
            proof.evidence = Some(ProofEvidence::from(ProofStrength::bounded(32)));
        }
        assert!(promoted_proof_evidence_for_transport(bounded).is_none());

        let mut unchecked = native_full_verifier_transport();
        if let Some(proof) = unchecked.proof_evidence.as_mut() {
            proof.strength = Some(ProofStrength {
                reasoning: trust_types::ReasoningKind::Smt,
                assurance: AssuranceLevel::Unchecked,
            });
            proof.evidence = Some(ProofEvidence::new(
                trust_types::ReasoningKind::Smt,
                AssuranceLevel::Unchecked,
            ));
        }
        assert!(promoted_proof_evidence_for_transport(unchecked).is_none());

        let mut mismatched = native_full_verifier_transport();
        if let Some(proof) = mismatched.proof_evidence.as_mut() {
            proof.strength = Some(ProofStrength::deductive());
            proof.evidence = Some(ProofEvidence::from(ProofStrength::inductive()));
        }
        assert!(
            promoted_proof_evidence_for_transport(mismatched).is_none(),
            "individually publication-grade strength and evidence must still describe one exact proof"
        );
    }

    #[test]
    fn publishable_native_proof_requires_canonical_artifact_digests() {
        let mut missing_digest = native_full_verifier_transport();
        if let Some(proof) = missing_digest.proof_evidence.as_mut() {
            proof.artifacts[0].digest = None;
        }
        assert!(promoted_proof_evidence_for_transport(missing_digest).is_none());

        let mut uppercase_digest = native_full_verifier_transport();
        if let Some(native_trust_ir) = uppercase_digest.native_trust_ir.as_mut() {
            native_trust_ir.artifacts[0].digest = Some(trust_types::TransportArtifactDigest {
                algorithm: "sha256".into(),
                value: "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA".into(),
            });
        }
        assert!(promoted_proof_evidence_for_transport(uppercase_digest).is_none());
    }

    #[test]
    fn publishable_native_proof_ignores_unmaterialized_legacy_structural_descriptors() {
        for suite in ["trust-mc", "trust-wp"] {
            let mut transport = native_transport_for_suite(suite);
            if let Some(proof) = transport.proof_evidence.as_mut() {
                proof.artifacts.push(trust_types::TransportEvidenceArtifact {
                    kind: "EngineInput".into(),
                    format: None,
                    artifact_id: Some("trust_ir-bundle".into()),
                    digest: Some(trust_types::TransportArtifactDigest {
                        algorithm: "trust_ir-stable-v1".into(),
                        value: "88b84220b47ae9f2b637ff5866553e98d28711d5199083ca6a93a83440445edc"
                            .into(),
                    }),
                    uri: Some(
                        "trust_ir-native://verification-bundle/88b84220b47ae9f2b637ff5866553e98d28711d5199083ca6a93a83440445edc"
                            .into(),
                    ),
                    materialization: None,
                    metadata: None,
                });
            }
            assert!(
                promoted_proof_evidence_for_transport(transport).is_some(),
                "{suite}: a non-load-bearing unmaterialized descriptor must not invalidate the exact DAG"
            );
        }
    }

    #[test]
    fn publishable_native_proof_rejects_trust_ir_stable_digest_on_load_bearing_artifacts() {
        // Trust: a non-cryptographic structural checksum is NOT an acceptable
        // content-address for an externally replayable proof. The load-bearing
        // proof artifacts (solver transcript / certificate / check / replay)
        // must remain sha256, even though structural artifacts may use
        // trust_ir-stable-v1. This is the soundness guardrail on the relaxation.
        for suite in ["trust-mc", "trust-wp"] {
            let mut transport = native_transport_for_suite(suite);
            if let Some(proof) = transport.proof_evidence.as_mut() {
                for artifact in proof.artifacts.iter_mut() {
                    if is_solver_transcript_artifact(artifact) {
                        artifact.digest = Some(trust_types::TransportArtifactDigest {
                            algorithm: "trust_ir-stable-v1".into(),
                            value:
                                "88b84220b47ae9f2b637ff5866553e98d28711d5199083ca6a93a83440445edc"
                                    .into(),
                        });
                    }
                }
            }
            assert!(
                promoted_proof_evidence_for_transport(transport).is_none(),
                "{suite}: a solver transcript content-addressed under trust_ir-stable-v1 must NOT publish"
            );
        }
    }

    #[test]
    fn publishable_native_proof_requires_transcript_and_replay_or_check_artifacts() {
        for suite in ["trust-mc", "trust-wp"] {
            let transport = native_transport_for_suite(suite);
            assert!(
                promoted_proof_evidence_for_transport(transport).is_some(),
                "{suite} CamelCase proof artifacts should normalize"
            );

            let mut missing_transcript = native_transport_for_suite(suite);
            if let Some(proof) = missing_transcript.proof_evidence.as_mut() {
                proof.artifacts.retain(|artifact| !is_solver_transcript_artifact(artifact));
            }
            assert!(promoted_proof_evidence_for_transport(missing_transcript).is_none(), "{suite}");

            let mut missing_replay_or_check = native_transport_for_suite(suite);
            if let Some(proof) = missing_replay_or_check.proof_evidence.as_mut() {
                proof.artifacts.retain(|artifact| !is_replay_or_check_artifact(artifact));
            }
            assert!(
                promoted_proof_evidence_for_transport(missing_replay_or_check).is_none(),
                "{suite}"
            );

            let mut unchecked_label = native_transport_for_suite(suite);
            if let Some(proof) = unchecked_label.proof_evidence.as_mut() {
                proof.artifacts[1].kind = "unchecked".into();
            }
            assert!(promoted_proof_evidence_for_transport(unchecked_label).is_none(), "{suite}");
        }
    }

    #[test]
    fn publishable_native_proof_rejects_error_transport_diagnostics() {
        let mut proof_error = native_full_verifier_transport();
        if let Some(proof) = proof_error.proof_evidence.as_mut() {
            proof.diagnostics.push(trust_types::TransportEvidenceDiagnostic {
                code: "proof.rejected".into(),
                severity: trust_types::TransportEvidenceDiagnosticSeverity::Error,
                message: "proof checker rejected replay".into(),
                detail: None,
            });
        }
        assert!(promoted_proof_evidence_for_transport(proof_error).is_none());

        let mut native_error = native_full_verifier_transport();
        if let Some(native_trust_ir) = native_error.native_trust_ir.as_mut() {
            native_trust_ir.diagnostics.push(trust_types::TransportEvidenceDiagnostic {
                code: "native_trust_ir.rejected".into(),
                severity: trust_types::TransportEvidenceDiagnosticSeverity::Error,
                message: "native TrustIr artifact was rejected".into(),
                detail: None,
            });
        }
        assert!(promoted_proof_evidence_for_transport(native_error).is_none());
    }

    #[test]
    fn terminal_lines_include_native_full_verifier_evidence_section() {
        let report = report_with_full_verifier_result(VerificationOutcome::Proved);
        let rendered = report.terminal_lines().join("\n");

        assert!(rendered.contains("Native full verifier evidence:"));
        assert!(rendered.contains("Transport obligations: 1 (1 proved"));
        assert!(rendered.contains("native full verifier status: Proved"));
    }

    #[test]
    fn terminal_lines_render_every_typed_certified_test_execution_state() {
        for (state, label) in [
            (CertifiedTestExecutionPhaseState::NotRequested, "not-requested"),
            (CertifiedTestExecutionPhaseState::Blocked, "blocked"),
            (CertifiedTestExecutionPhaseState::Started, "started"),
            (CertifiedTestExecutionPhaseState::CargoInvocationExited, "cargo-invocation-exited"),
        ] {
            let mut report = report_with_full_verifier_result(VerificationOutcome::Proved);
            report.test_execution = Some(CertifiedTestExecutionReport {
                schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.to_string(),
                completion_scope:
                    CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
                requested: true,
                scope: trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.into(),
                compile_only: state == CertifiedTestExecutionPhaseState::NotRequested,
                phase_a_status: 0,
                phase_a_success: true,
                phase_b_state: state,
                blocker: None,
                phase_b_exit: None,
                authorized_executables: Vec::new(),
                authorized_inventory_sha256: None,
                target_directory: None,
            });

            let execution_lines = report
                .terminal_lines()
                .into_iter()
                .filter(|line| line.starts_with("Certified test execution:"))
                .collect::<Vec<_>>();
            assert_eq!(execution_lines.len(), 1, "state={state:?}: {execution_lines:?}");
            assert!(
                execution_lines[0].contains(&format!("state={label}")),
                "state={state:?}: {}",
                execution_lines[0]
            );
        }

        let report = report_with_full_verifier_result(VerificationOutcome::Proved);
        assert!(
            report
                .terminal_lines()
                .iter()
                .all(|line| !line.starts_with("Certified test execution:")),
            "non-test reports must not invent an execution state"
        );
    }

    #[test]
    fn certified_test_execution_terminal_line_surfaces_available_phase_and_inventory_details() {
        let executable = CertifiedTestExecutableReport {
            target: "demo::integration".into(),
            path: "/private/target/demo-test".into(),
            sha256: "a".repeat(64),
            size: 42,
        };
        let completed = CertifiedTestExecutionReport {
            schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.to_string(),
            completion_scope: CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
            requested: true,
            scope: trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.into(),
            compile_only: false,
            phase_a_status: 0,
            phase_a_success: true,
            phase_b_state: CertifiedTestExecutionPhaseState::CargoInvocationExited,
            blocker: None,
            phase_b_exit: Some(101),
            authorized_executables: vec![executable.clone()],
            authorized_inventory_sha256: Some("b".repeat(64)),
            target_directory: Some("/private/target".into()),
        };
        assert_eq!(
            certified_test_execution_terminal_line(&completed),
            "Certified test execution: schema=trust.certified-test-execution.v2 completion_scope=top-level-cargo-child-exit-only-v1 state=cargo-invocation-exited requested=true compile_only=false phase_a_exit=0 phase_a_success=true authorized_executables=1 phase_b_exit=101"
        );

        let blocked = CertifiedTestExecutionReport {
            schema: completed.schema.clone(),
            completion_scope: completed.completion_scope,
            requested: true,
            scope: completed.scope.clone(),
            compile_only: false,
            phase_a_status: 2,
            phase_a_success: false,
            phase_b_state: CertifiedTestExecutionPhaseState::Blocked,
            blocker: Some("phase A failed\nbefore execution".into()),
            phase_b_exit: None,
            authorized_executables: Vec::new(),
            authorized_inventory_sha256: None,
            target_directory: None,
        };
        assert_eq!(
            certified_test_execution_terminal_line(&blocked),
            "Certified test execution: schema=trust.certified-test-execution.v2 completion_scope=top-level-cargo-child-exit-only-v1 state=blocked requested=true compile_only=false phase_a_exit=2 phase_a_success=false blocker=\"phase A failed\\nbefore execution\""
        );
    }

    #[test]
    fn terminal_lines_surface_cache_hit_rate_when_obligations_replayed() {
        // Trust (verify-cache): cached == 0 emits no cache line.
        let report = report_with_full_verifier_result(VerificationOutcome::Proved);
        assert_eq!(report.cached, 0);
        assert!(
            !report.terminal_lines().join("\n").contains("Cache:"),
            "no cache line when nothing was replayed"
        );

        // cached > 0 emits an informational hit-rate line. It must NOT change the
        // proof verdict (no proof credit) — the Summary line is unaffected.
        let mut replayed = report_with_full_verifier_result(VerificationOutcome::Proved);
        replayed.cached = 1; // this helper builds total == 1
        let rendered = replayed.terminal_lines().join("\n");
        assert!(
            rendered.contains(
                "Cache: 1 of 1 obligation(s) replayed from verification cache (100% hit rate)"
            ),
            "cache hit-rate line missing or malformed: {rendered}"
        );
        assert!(rendered.contains("Summary: 1 proved"), "cache line must not alter the verdict");
    }

    /// Trust (assertion-grade coverage, roadmap §4.1): the human report always
    /// carries a coverage line — complete, shortfall (loud, fail-closed), or
    /// honestly unknown when an OLDER compiler emitted no coverage row.
    #[test]
    fn terminal_lines_surface_coverage_complete_shortfall_and_unknown() {
        // Absent coverage (older toolchain): reported as unknown, never omitted
        // and never claimed complete.
        let report = report_with_full_verifier_result(VerificationOutcome::Proved);
        assert_eq!(report.coverage, None);
        let rendered = report.terminal_lines().join("\n");
        assert!(
            rendered.contains("Coverage: unknown (compiler emitted no coverage_summary"),
            "absent coverage must be reported as unknown: {rendered}"
        );

        // Complete coverage: processed/eligible surfaced.
        let mut complete = report_with_full_verifier_result(VerificationOutcome::Proved);
        complete.coverage = Some(trust_types::VerificationCoverage::from_counts(12, 12));
        let rendered = complete.terminal_lines().join("\n");
        assert!(
            rendered.contains("Coverage: 12/12 eligible function bodies verified (complete)"),
            "complete coverage line missing: {rendered}"
        );

        // Shortfall: the loud never-verified line, fail-closed wording included.
        let mut shortfall = report_with_full_verifier_result(VerificationOutcome::Proved);
        shortfall.coverage = Some(trust_types::VerificationCoverage::from_counts(12, 9));
        let rendered = shortfall.terminal_lines().join("\n");
        assert!(
            rendered.contains("coverage shortfall: 3 function(s) were never verified"),
            "shortfall line missing: {rendered}"
        );
        assert!(rendered.contains("Coverage: 9/12"), "shortfall counts missing: {rendered}");
    }

    /// Trust (T9 contract-panic): the summary line renders the contract-panic
    /// count UNCONDITIONALLY (0 included), and a success resting on a contract
    /// panic is labeled a CONDITIONAL pass — the count is never silent.
    #[test]
    fn terminal_lines_always_show_contract_panic_count() {
        // Zero case: the count is still printed.
        let report = report_with_full_verifier_result(VerificationOutcome::Proved);
        let rendered = report.terminal_lines().join("\n");
        assert!(
            rendered.contains("0 contract-panic"),
            "summary must always render the contract-panic count: {rendered}"
        );
        assert_eq!(report.terminal_status_label(), "PASS");

        // Conditional case: a proved row + a rewritten contract-panic row.
        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![
                native_full_verifier_transport_result(),
                gate_like_result("contract-panic:matched", VerificationOutcome::Failed),
            ],
            vec![],
        ));
        // The partition puts the contract-panic row in its own bucket; success
        // mirrors the default gate (no genuine failure/unknown).
        assert_eq!(report.failed, 0, "contract-panic rows are not genuine failures");
        assert_eq!(report.contract_panics, 1);
        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_failed, 0);
        assert_eq!(canonical.summary.total_unknown, 1);
        let rendered = report.terminal_lines().join("\n");
        assert!(
            rendered.contains("1 contract-panic"),
            "summary must render the nonzero contract-panic count: {rendered}"
        );
        let label = report.terminal_status_label();
        assert!(
            label.starts_with("PASS (conditional:") && label.contains("1 contract-panic"),
            "a pass resting on a contract panic must be labeled conditional: {label}"
        );
    }

    /// Minimal result row for gate/partition-shaped report tests.
    fn gate_like_result(kind: &str, outcome: VerificationOutcome) -> VerificationResult {
        VerificationResult {
            function: "crate::f".into(),
            kind: kind.into(),
            message: "m".into(),
            outcome,
            backend: "ay".into(),
            time_ms: Some(1),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        }
    }

    #[test]
    fn hardened_tags_parse_as_hardened_report_categories() {
        let report = report_with_result(
            VerificationResult {
                function: "crate::paths::render".into(),
                kind: "hardened_byte_loss".into(),
                message: "hardened boundary (byte_loss): lossy OS/path conversion must be explicit"
                    .into(),
                outcome: VerificationOutcome::Proved,
                backend: "ay-smtlib".into(),
                time_ms: Some(3),
                location: None,
                counterexample: None,
                reason: None,
                raw_line: String::new(),
            },
            VerificationOutcome::Proved,
        );

        let trust_report = report.to_trust_report();
        let obligation = &trust_report.functions[0].obligations[0];
        assert_eq!(obligation.kind, "hardened_byte_loss");
        assert!(obligation.description.contains("hardened boundary (byte_loss)"));
        assert!(obligation.description.contains("lossy OS/path conversion must be explicit"));

        let json = serde_json::to_value(&trust_report).expect("serialize trust report");
        assert_eq!(json["functions"][0]["obligations"][0]["kind"], "hardened_byte_loss");
    }

    #[test]
    fn hardened_results_populate_report_context_inventory_and_counts() {
        let report = report_with_results_and_diagnostics(
            vec![
                VerificationResult {
                    function: "crate::paths::render".into(),
                    kind: "hardened_byte_loss".into(),
                    message: "hardened boundary (byte_loss): Path::as_os_str: byte-exact rendering"
                        .into(),
                    outcome: VerificationOutcome::Proved,
                    backend: "ay-smtlib".into(),
                    time_ms: Some(3),
                    location: Some(SourceSpan {
                        file: "src/path.rs".into(),
                        line_start: 17,
                        col_start: 9,
                        line_end: 17,
                        col_end: 32,
                    }),
                    counterexample: None,
                    reason: None,
                    raw_line: String::new(),
                },
                VerificationResult {
                    function: "crate::paths::rename".into(),
                    kind: "hardened_raw_path_api".into(),
                    message: "raw rename needs a direntry identity contract".into(),
                    outcome: VerificationOutcome::Failed,
                    backend: "ay-smtlib".into(),
                    time_ms: Some(8),
                    location: None,
                    counterexample: None,
                    reason: None,
                    raw_line: String::new(),
                },
            ],
            vec![CompilerDiagnostic {
                level: "note".into(),
                message: "targo trust: hardened profile `coreutils_hardened` enabled".into(),
            }],
        );

        let trust_report = report.to_trust_report();
        let hardened = trust_report.hardened.as_ref().expect("hardened report context");
        let profile = hardened.profile.as_ref().expect("hardened profile");
        assert_eq!(profile.name.as_deref(), Some("coreutils_hardened"));
        assert_eq!(
            profile.enabled_categories,
            hardened_profile_enabled_categories(Some("coreutils_hardened"), &BTreeSet::new())
        );

        let summary = hardened.summary.as_ref().expect("hardened summary");
        // Trust (green front door E4): the denominator counts only PROVED,
        // non-mandate hardened rows. Of the two rows here (one Proved byte_loss,
        // one Failed raw_path_api), only the proved one sits in the denominator;
        // the refuted row still fails the run through the outcome gate. Both
        // rows remain in the boundary inventory (nothing hidden).
        assert_eq!(summary.hardened_obligations, 1);
        assert_eq!(summary.proved_hardened_obligations, 0);
        assert_eq!(summary.inventory_entries, 2);
        assert_eq!(summary.model_assumptions, 0);
        assert_eq!(summary.proof_evidence_entries, 0);
        assert_eq!(
            hardened.assurance.as_ref().and_then(|assurance| assurance.level.as_deref()),
            Some("inventory_only")
        );

        let inventory: Vec<&HardenedBoundaryInventoryEntry> = hardened
            .boundary_inventory
            .iter()
            .filter(|entry| entry.role == HardenedBoundaryInventoryRole::Inventory)
            .collect();
        assert_eq!(inventory.len(), 2);
        assert!(inventory.iter().any(|entry| entry.category == "byte_loss"
            && entry.boundary == "Path::as_os_str"
            && entry.function.as_deref() == Some("crate::paths::render")));
    }

    #[test]
    #[ignore = "pre-existing at HEAD (2026-07-02): the publishable-native-proof gate (structured_native_proof_is_publishable, hardened by the un-forgeable-Proved work c4ccc46da5/9f6a12cc19) rejects this fixture's evidence and proof_evidence stays None; needs a fixture upgrade to the gate's current artifact contract — tracked in docs/design-notes/2026-07-02-assumption-ledger-stage1-plan.md follow-ups"]
    fn hardened_context_links_structured_model_assumptions_and_proof_evidence() {
        let report = report_with_results_and_diagnostics(
            vec![hardened_transport_result_with_context()],
            Vec::new(),
        );

        let trust_report = report.to_trust_report();
        let hardened = trust_report.hardened.as_ref().expect("hardened report context");
        let summary = hardened.summary.as_ref().expect("hardened summary");
        assert_eq!(summary.hardened_obligations, 1);
        assert_eq!(summary.proved_hardened_obligations, 1);
        assert_eq!(summary.inventory_entries, 1);
        assert_eq!(summary.model_assumptions, 1);
        assert_eq!(summary.proof_evidence_entries, 1);
        assert_eq!(
            hardened.assurance.as_ref().and_then(|assurance| assurance.level.as_deref()),
            Some("proof_backed")
        );

        let obligation = &trust_report.functions[0].obligations[0];
        let evidence = obligation.proof_evidence.as_ref().expect("hardened proof evidence");
        assert_eq!(evidence.proof_id.as_deref(), Some("9"));
        assert_eq!(
            evidence.native_id.as_deref(),
            Some("trust_ir-native-trust-wp-request-8-proof-9")
        );
        assert_eq!(evidence.strength, ProofStrength::deductive());
        assert!(!evidence.artifacts.is_empty());
        assert!(evidence.native_trust_ir.is_some());

        let assumption = hardened
            .boundary_inventory
            .iter()
            .find(|entry| entry.role == HardenedBoundaryInventoryRole::ModelAssumption)
            .expect("model assumption entry");
        assert_eq!(assumption.category, "byte_loss");
        assert_eq!(assumption.boundary, "unix.model_assumption");
        assert_eq!(assumption.obligation_id.as_deref(), Some("crate::paths::render:hardened0"));
        assert!(
            assumption
                .description
                .as_deref()
                .is_some_and(|description| description.contains("OsStr preserves raw bytes"))
        );

        let proof = hardened
            .boundary_inventory
            .iter()
            .find(|entry| entry.role == HardenedBoundaryInventoryRole::ProofEvidence)
            .expect("proof evidence entry");
        assert_eq!(proof.category, "byte_loss");
        assert_eq!(proof.boundary, "Path::as_os_str");
        assert_eq!(proof.proof_evidence_id.as_deref(), Some("proof-byte-loss"));
        assert_eq!(proof.source.as_deref(), Some("ay-smtlib"));
    }

    #[test]
    fn hardened_proof_gate_fails_when_native_evidence_is_inventory_only() {
        let mut report = report_with_result(
            VerificationResult {
                function: "crate::paths::render".into(),
                kind: "hardened_byte_loss".into(),
                message: "lossy OS/path conversion must be explicit".into(),
                outcome: VerificationOutcome::Proved,
                backend: "ay-smtlib".into(),
                time_ms: Some(3),
                location: None,
                counterexample: None,
                reason: None,
                raw_line: String::new(),
            },
            VerificationOutcome::Proved,
        );
        report.config.hardened = true;
        report.config.trust_profile = Some("unix_hardened".to_string());

        let failure = report
            .hardened_proof_gate_failure()
            .expect("hardened native report without proof evidence must fail closed");
        assert_eq!(failure.hardened_obligations, 1);
        assert_eq!(failure.proof_evidence_entries, 0);
        assert_eq!(report.terminal_status_label(), "FAIL");
    }

    #[test]
    fn hardened_proof_gate_allows_publishable_native_proof_evidence() {
        let mut report = with_live_transport_authority(report_with_result(
            hardened_transport_result_with_context(),
            VerificationOutcome::Proved,
        ));
        report.config.hardened = true;
        report.config.trust_profile = Some("unix_hardened".to_string());

        assert_eq!(report.hardened_proof_gate_failure(), None);
        assert_eq!(report.terminal_status_label(), "PASS");
    }

    #[test]
    fn clean_cic_v2_identity_is_preserved_raw_obligation_and_hardened_inventory() {
        let raw = clean_cic_hardened_result();
        let structured = structured_transport_evidence(&raw).expect("structured compiler row");
        let raw_proof = structured.proof_evidence.as_ref().expect("raw CleanCic proof");
        assert!(clean_cic_transport_proof_is_publishable(&raw, raw_proof));
        let raw_id = raw_proof.proof_id.clone().expect("content-addressed raw proof ID");
        assert_eq!(
            raw_proof.artifacts[0].artifact_id.as_deref(),
            Some(raw_id.as_str()),
            "raw proof and artifact identities must agree"
        );

        let mut report = report_with_result(raw, VerificationOutcome::Proved);
        report.config.hardened = true;
        report.config.trust_profile = Some("unix_hardened".into());
        let report = with_live_transport_authority(report);
        assert_eq!(report.hardened_proof_gate_failure(), None);
        assert_eq!(report.terminal_status_label(), "PASS");

        let canonical = report.to_trust_report();
        let obligation = &canonical.functions[0].obligations[0];
        let obligation_proof = obligation.proof_evidence.as_ref().expect("obligation proof");
        assert_eq!(obligation_proof.proof_id.as_deref(), Some(raw_id.as_str()));
        assert_eq!(obligation_proof.native_trust_ir, None);

        let hardened = canonical.hardened.as_ref().expect("hardened context");
        let summary = hardened.summary.as_ref().expect("hardened summary");
        assert_eq!(summary.hardened_obligations, 1);
        assert_eq!(summary.proof_evidence_entries, 1);
        let inventory_proof = hardened
            .boundary_inventory
            .iter()
            .find(|entry| entry.role == HardenedBoundaryInventoryRole::ProofEvidence)
            .expect("hardened proof inventory entry");
        assert_eq!(inventory_proof.proof_evidence_id.as_deref(), Some(raw_id.as_str()));
        let inventory_entry_id = format!("hardened-proof-evidence:{raw_id}");
        assert_eq!(inventory_proof.id.as_deref(), Some(inventory_entry_id.as_str()));
    }

    #[test]
    fn clean_cic_v2_rejects_missing_forged_and_mismatched_identities() {
        let assert_rejected = |transport: trust_types::TransportObligationResult, label: &str| {
            let result = transport_to_verification_result("crate::paths::render", &transport);
            let structured =
                structured_transport_evidence(&result).expect("structured CleanCic row");
            let proof = structured.proof_evidence.as_ref().expect("CleanCic proof");
            assert!(
                !clean_cic_transport_proof_is_publishable(&result, proof),
                "{label} identity must fail closed"
            );
            assert!(
                promoted_proof_evidence_for_transport(transport).is_none(),
                "{label} identity must not reach obligation publication"
            );
        };

        let mut missing = clean_cic_hardened_transport();
        missing.proof_evidence.as_mut().expect("proof").proof_id = None;
        assert_rejected(missing, "missing proof");

        let mut missing_artifact = clean_cic_hardened_transport();
        missing_artifact.proof_evidence.as_mut().expect("proof").artifacts[0].artifact_id = None;
        assert_rejected(missing_artifact, "missing artifact");

        let forged_id = format!("clean-cic:v2:{}", "0".repeat(64));
        let mut forged = clean_cic_hardened_transport();
        let forged_proof = forged.proof_evidence.as_mut().expect("proof");
        forged_proof.proof_id = Some(forged_id.clone());
        forged_proof.artifacts[0].artifact_id = Some(forged_id);
        assert_rejected(forged, "coherently forged proof/artifact");

        let mut mismatched = clean_cic_hardened_transport();
        mismatched.proof_evidence.as_mut().expect("proof").artifacts[0].artifact_id =
            Some(format!("clean-cic:v2:{}", "1".repeat(64)));
        assert_rejected(mismatched, "proof/artifact mismatch");

        // A coherently content-addressed arbitrary JSON payload is not a
        // CleanCic certificate, even when every envelope identifier matches.
        let mut wrong_schema = clean_cic_hardened_transport();
        let proof = wrong_schema.proof_evidence.as_mut().expect("proof");
        let metadata = serde_json::json!({"CleanCic": {"term": [1], "context": [2]}});
        let bytes = serde_json::to_vec(&metadata).expect("serialize forged payload");
        let digest = trustc_domain_length_bound_sha256_hex("trustc.transport-clean-cic.v2", &bytes);
        let forged_id = format!("clean-cic:v2:{digest}");
        proof.proof_id = Some(forged_id.clone());
        proof.artifacts[0].artifact_id = Some(forged_id);
        proof.artifacts[0].digest.as_mut().expect("digest").value = digest.clone();
        proof.artifacts[0].uri = Some(format!("trust-certify://clean-cic/{digest}"));
        proof.artifacts[0].metadata = Some(metadata);
        assert_rejected(wrong_schema, "content-addressed wrong schema");
    }

    #[test]
    fn hardened_duplicate_representative_prefers_publishable_clean_cic() {
        for publishable_first in [false, true] {
            let mut evidence_less = clean_cic_hardened_transport();
            evidence_less.proof_evidence.as_mut().expect("proof").proof_id = None;
            let evidence_less =
                transport_to_verification_result("crate::paths::render", &evidence_less);
            let publishable = clean_cic_hardened_result();
            let results = if publishable_first {
                vec![publishable, evidence_less]
            } else {
                vec![evidence_less, publishable]
            };

            let mut report = report_with_results_and_diagnostics(results, Vec::new());
            report.config.hardened = true;
            report.config.trust_profile = Some("unix_hardened".into());
            let report = with_live_transport_authority(report);

            let canonical = report.to_trust_report();
            let hardened = canonical.hardened.as_ref().expect("hardened context");
            let summary = hardened.summary.as_ref().expect("hardened summary");
            assert_eq!(summary.hardened_obligations, 1);
            assert_eq!(summary.proof_evidence_entries, 1);
            assert_eq!(
                hardened
                    .boundary_inventory
                    .iter()
                    .filter(|entry| entry.role == HardenedBoundaryInventoryRole::Inventory)
                    .count(),
                1,
                "duplicate exact-claim rows must produce one boundary representative"
            );
            assert_eq!(
                hardened
                    .boundary_inventory
                    .iter()
                    .filter(|entry| entry.role == HardenedBoundaryInventoryRole::ProofEvidence)
                    .count(),
                1,
                "the publishable CleanCic twin must win representative selection"
            );
        }
    }

    #[test]
    fn hardened_proof_gate_ignores_non_hardened_or_empty_runs() {
        let mut ordinary =
            report_with_result(result_with_location(None), VerificationOutcome::Proved);
        ordinary.config.hardened = true;
        ordinary.config.trust_profile = Some("unix_hardened".to_string());
        assert_eq!(ordinary.hardened_proof_gate_failure(), None);

        ordinary.config.hardened = false;
        ordinary.results = vec![VerificationResult {
            function: "crate::paths::render".into(),
            kind: "hardened_byte_loss".into(),
            message: "lossy OS/path conversion must be explicit".into(),
            outcome: VerificationOutcome::Proved,
            backend: "ay-smtlib".into(),
            time_ms: Some(3),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        }];
        assert_eq!(ordinary.hardened_proof_gate_failure(), None);
    }

    /// A compiler-declared design-mandate row: the transport row carries the
    /// structured `design_mandate` bit the compiler set for a hardened VC with
    /// a tautology violation formula (e.g. "[unsafe] missing SAFETY comment").
    fn design_mandate_result() -> VerificationResult {
        let transport = trust_types::TransportObligationResult {
            obligation_id: None,
            claim_digest_sha256: None,
            kind: "hardened_unsafe_operation".into(),
            typed_kind: None,
            description: "assertion: [unsafe] missing SAFETY comment on unsafe block".into(),
            location: Some(SourceSpan {
                file: "src/lib.rs".into(),
                line_start: 4,
                col_start: 5,
                line_end: 4,
                col_end: 20,
            }),
            outcome: trust_types::Outcome::Unknown,
            solver: "ay-in-process".into(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: Some("design mandate is not mechanically dischargeable".into()),
            design_mandate: true,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
        };
        transport_to_verification_result("crate::uses_unsafe", &transport)
    }

    fn full_verifier_design_mandate_result() -> VerificationResult {
        let mut result = design_mandate_result();
        result.function = "std::io::stdio::_print".into();
        result.kind = "hardened_process_semantics".into();
        result.message = "native full verifier: process semantics require a design mandate".into();
        result.backend = "trust-full-verifier".into();
        result
    }

    #[test]
    fn hardened_proof_gate_excludes_compiler_design_mandate_rows_from_denominator() {
        // A design mandate can never carry proof evidence BY CONSTRUCTION, so
        // it must not sit in the proof-evidence denominator — but it must stay
        // in the boundary inventory (reported, never hidden).
        let mut report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![design_mandate_result()],
            vec![],
        ));
        report.config.hardened = true;
        report.config.trust_profile = Some("unix_hardened".to_string());

        assert_eq!(report.hardened_proof_gate_failure(), None);

        let trust_report = report.to_trust_report();
        let hardened = trust_report.hardened.as_ref().expect("hardened report context");
        let summary = hardened.summary.as_ref().expect("hardened summary");
        assert_eq!(summary.hardened_obligations, 0);
        assert_eq!(summary.proof_evidence_entries, 0);
        assert_eq!(summary.inventory_entries, 1, "mandate rows stay in the inventory");
    }

    #[test]
    fn hardened_evidence_less_proved_claim_is_downgraded_before_gate() {
        // A compiler Proved label without publication evidence is normalized to
        // Unknown before Targo can mint row authority. The hardened gate then
        // has no proof claim to accept, and the canonical verdict remains
        // inconclusive beside the separately classified design mandate.
        let mut report = report_with_results_and_diagnostics(
            vec![
                design_mandate_result(),
                VerificationResult {
                    function: "crate::paths::render".into(),
                    kind: "hardened_byte_loss".into(),
                    message: "lossy OS/path conversion must be explicit".into(),
                    outcome: VerificationOutcome::Proved,
                    backend: "ay-smtlib".into(),
                    time_ms: Some(3),
                    location: None,
                    counterexample: None,
                    reason: None,
                    raw_line: String::new(),
                },
            ],
            vec![],
        );
        report.config.hardened = true;
        report.config.trust_profile = Some("unix_hardened".to_string());
        let report = with_live_transport_authority(report);

        assert_eq!(report.results[1].outcome, VerificationOutcome::Unknown);
        assert_eq!(report.hardened_proof_gate_failure(), None);
        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_proved, 0);
        assert_eq!(canonical.summary.total_unknown, 1);
        assert_eq!(canonical.summary.total_design_requirements, 1);
        assert_eq!(canonical.summary.verdict, trust_types::CrateVerdict::Inconclusive);
    }

    #[test]
    fn design_mandate_bit_never_comes_from_row_text() {
        // A row whose TEXT looks like a mandate but whose transport row does
        // not carry the compiler bit stays in the denominator: targo must not
        // guess mandates from text. The row is PROVED so the E4 proved-only
        // denominator narrowing does not exclude it for an unrelated reason —
        // the only thing that could drop it from the denominator is a (wrong)
        // text-guessed mandate exclusion, which must not happen. With no
        // publishable evidence the gate then fails 0/1.
        let mut report = report_with_results_and_diagnostics(
            vec![VerificationResult {
                function: "crate::uses_unsafe".into(),
                kind: "hardened_unsafe_operation".into(),
                message: "assertion: [unsafe] missing SAFETY comment on unsafe block".into(),
                outcome: VerificationOutcome::Proved,
                backend: "ay-in-process".into(),
                time_ms: Some(0),
                location: None,
                counterexample: None,
                reason: None,
                raw_line: String::new(),
            }],
            vec![],
        );
        report.config.hardened = true;
        report.config.trust_profile = Some("unix_hardened".to_string());

        let failure = report
            .hardened_proof_gate_failure()
            .expect("text-only mandate lookalikes must stay in the denominator");
        assert_eq!(failure.hardened_obligations, 1);
    }

    #[test]
    fn hardened_unknown_row_is_inconclusive_not_fail_after_e4() {
        // Trust (green front door E4 / F10): a hardened-category row that is
        // UNKNOWN (not a design mandate, not proved) must NOT fail the hardened
        // proof-evidence gate — the numerator can only ever be minted from a
        // PROVED row, so an unknown hardened row could only mislabel a run in
        // which NOTHING was refuted as FAIL. Post-E4 the denominator drops it,
        // so the gate returns None and the terminal label is INCONCLUSIVE.
        let mut report = report_with_results_and_diagnostics(
            vec![VerificationResult {
                function: "crate::paths::render".into(),
                kind: "hardened_process_semantics".into(),
                message: "SIGPIPE default disposition boundary".into(),
                outcome: VerificationOutcome::Unknown,
                backend: "ay-in-process".into(),
                time_ms: Some(0),
                location: None,
                counterexample: None,
                reason: None,
                raw_line: String::new(),
            }],
            vec![],
        );
        report.config.hardened = true;
        report.config.trust_profile = Some("unix_hardened".to_string());
        // The compiler did not abort on an unknown — it returned UNKNOWN and
        // exited 0. (The helper conflates targo-success with compiler-exit; the
        // real compiler exit for an unknown-only run is 0.)
        report.exit_code = 0;

        // The hardened evidence gate does not fire (denominator is empty).
        assert_eq!(report.hardened_proof_gate_failure(), None);
        // The row is a genuine unknown, so the run is not a (conditional) pass:
        // base_success is false, but the label is INCONCLUSIVE, never FAIL.
        assert!(!report.success);
        assert_eq!(report.terminal_status_label(), "INCONCLUSIVE");
    }

    #[test]
    fn to_trust_report_labels_only_compiler_design_mandates_as_design_requirements() {
        // A genuinely PROVED hardened row must render as proved — the
        // fabricated `Bool(true)` formula used to mislabel every hardened row
        // as design_requirement. Only the compiler-declared mandate row keeps
        // that classification.
        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![hardened_transport_result_with_context(), design_mandate_result()],
            vec![],
        ));

        let trust_report = report.to_trust_report();
        let outcomes: Vec<&ObligationOutcome> = trust_report
            .functions
            .iter()
            .flat_map(|function| function.obligations.iter().map(|obligation| &obligation.outcome))
            .collect();
        assert_eq!(outcomes.len(), 2);
        assert!(
            outcomes.iter().any(|outcome| matches!(outcome, ObligationOutcome::Proved { .. })),
            "genuinely proved hardened rows must render as proved, got {outcomes:?}"
        );
        assert!(
            outcomes
                .iter()
                .any(|outcome| matches!(outcome, ObligationOutcome::DesignRequirement { .. })),
            "compiler-declared mandate rows must render as design_requirement, got {outcomes:?}"
        );
    }

    #[test]
    fn authorized_full_verifier_mandate_keeps_design_requirement_classification() {
        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![full_verifier_design_mandate_result()],
            vec![],
        ));

        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_design_requirements, 1);
        assert_eq!(canonical.summary.total_unknown, 0);
        assert!(
            canonical.functions.iter().flat_map(|function| &function.obligations).any(
                |obligation| matches!(
                    &obligation.outcome,
                    ObligationOutcome::DesignRequirement { .. }
                )
            ),
            "an authorized full-verifier mandate must not be preempted by the ordinary Assertion mapping"
        );
        assert!(
            report.canonical_report_matches_internal_state(&canonical),
            "canonical mandate counts must remain aligned with the sealed internal partition"
        );
    }

    #[test]
    fn split_brain_typed_row_cannot_mint_design_mandate_credit() {
        let mut result = design_mandate_result();
        let mut evidence = structured_transport_evidence(&result).expect("structured mandate");
        evidence.typed_kind = Some(Box::new(VcKind::Postcondition));
        crate::types::replace_structured_transport_evidence(&mut result, &evidence)
            .expect("replace structured evidence");
        assert!(!transport_design_mandate(&result));

        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![result],
            vec![],
        ));
        assert_eq!(report.mandated, 0);
        assert_eq!(report.unknown, 1);
        assert!(!report.success);

        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_design_requirements, 0);
        assert_eq!(canonical.summary.total_unknown, 1);
        assert_eq!(canonical.summary.verdict, trust_types::CrateVerdict::Inconclusive);
        assert!(
            canonical
                .functions
                .iter()
                .flat_map(|function| &function.obligations)
                .all(|obligation| matches!(obligation.outcome, ObligationOutcome::Unknown { .. }))
        );
    }

    #[test]
    fn exact_non_hardened_kind_cannot_mint_design_mandate_credit() {
        let mut result = design_mandate_result();
        result.kind = "divzero".to_string();
        result.message = "division by zero".to_string();
        let mut evidence = structured_transport_evidence(&result).expect("structured mandate");
        evidence.typed_kind = Some(Box::new(VcKind::DivisionByZero));
        crate::types::replace_structured_transport_evidence(&mut result, &evidence)
            .expect("replace structured evidence");
        assert_eq!(exact_transport_vc_kind(&result), Ok(Some(VcKind::DivisionByZero)));
        assert!(!transport_design_mandate(&result));

        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![result],
            vec![],
        ));
        assert_eq!(report.mandated, 0);
        assert_eq!(report.unknown, 1);
        assert!(!report.success);

        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_design_requirements, 0);
        assert_eq!(canonical.summary.total_unknown, 1);
        assert_eq!(canonical.summary.verdict, trust_types::CrateVerdict::Inconclusive);
    }

    #[test]
    fn unauthorized_full_verifier_mandate_is_unknown_without_design_credit() {
        let report = report_with_results_and_diagnostics(
            vec![full_verifier_design_mandate_result()],
            vec![],
        );

        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_design_requirements, 0);
        assert_eq!(canonical.summary.total_unknown, 1);
        assert!(canonical.functions.iter().flat_map(|function| &function.obligations).all(
            |obligation| !matches!(
                &obligation.outcome,
                ObligationOutcome::DesignRequirement { .. }
            )
        ));
    }

    fn typed_transport_result(
        function: &str,
        kind: VcKind,
        backend: &str,
        outcome: trust_types::Outcome,
    ) -> VerificationResult {
        let transport = trust_types::TransportObligationResult {
            obligation_id: None,
            claim_digest_sha256: None,
            kind: kind.transport_tag(),
            typed_kind: Some(Box::new(kind.clone())),
            description: kind.description(),
            location: None,
            outcome,
            solver: backend.to_string(),
            time_ms: 17,
            counterexample: None,
            counterexample_model: None,
            reason: Some("typed transport fixture".to_string()),
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
        };
        transport_to_verification_result(function, &transport)
    }

    #[test]
    fn untyped_full_verifier_rows_fail_closed_without_runtime_fallback() {
        assert!(matches!(
            report_vc_kind(&full_verifier_result(VerificationOutcome::Unknown)),
            VcKind::UnsupportedMir { .. }
        ));
    }

    #[test]
    fn exact_typed_unsupported_mir_rejects_every_favorable_outcome() {
        for outcome in [trust_types::Outcome::Proved, trust_types::Outcome::RuntimeChecked] {
            let result = typed_transport_result(
                "crate::unsupported",
                VcKind::UnsupportedMir {
                    kind: "OpaqueSemanticGap".into(),
                    detail: "no exact verifier semantics".into(),
                },
                "ay",
                outcome,
            );
            assert_eq!(result.outcome, VerificationOutcome::Unknown, "{outcome}");
            assert!(result.reason.as_deref().is_some_and(|reason| {
                reason.contains("classified the obligation as unsupported MIR")
                    && reason.contains("downgraded before publication")
            }));

            let canonical = with_live_transport_authority(report_with_result(
                result,
                VerificationOutcome::Unknown,
            ))
            .to_trust_report();
            let obligation = &canonical.functions[0].obligations[0];
            assert_eq!(obligation.kind, "unsupported_mir");
            assert!(matches!(obligation.outcome, ObligationOutcome::Unknown { .. }));
            assert!(obligation.proof_evidence.is_none());
            assert_eq!(canonical.summary.total_proved, 0);
            assert_eq!(canonical.summary.total_runtime_checked, 0);
            assert_eq!(canonical.summary.total_unknown, 1);
        }
    }

    #[test]
    fn typed_transport_roundtrips_every_compact_family_across_proof_levels() {
        use trust_types::{
            FairnessConstraint, LivenessProperty, ProofLevel, StateMachineMetadata,
            TemporalOperator, Ty,
        };

        let signed32 = Ty::Int { width: 32, signed: true };
        let unsigned8 = Ty::Int { width: 8, signed: false };
        let machine = StateMachineMetadata {
            states: vec!["Idle".into(), "Ready".into()],
            init_states: vec![0],
            transitions: vec![(0, "wake".into(), 1)],
            labels: [(0, vec!["idle".into()]), (1, vec!["ready".into()])].into_iter().collect(),
        };
        let fairness =
            FairnessConstraint::Strong { action: "wake".into(), vars: vec!["state".into()] };
        let cases = vec![
            (
                VcKind::ArithmeticOverflow {
                    op: trust_types::BinOp::Add,
                    operand_tys: (signed32.clone(), signed32.clone()),
                },
                "arithmetic_overflow_add",
                ProofLevel::L0Safety,
                "ay-in-process",
            ),
            (
                VcKind::ShiftOverflow {
                    op: trust_types::BinOp::Shl,
                    operand_ty: signed32.clone(),
                    shift_ty: unsigned8.clone(),
                },
                "shift_overflow_shl",
                ProofLevel::L0Safety,
                "ay-in-process",
            ),
            (VcKind::DivisionByZero, "division_by_zero", ProofLevel::L0Safety, "ay"),
            (VcKind::RemainderByZero, "remainder_by_zero", ProofLevel::L0Safety, "ay"),
            (VcKind::IndexOutOfBounds, "index_out_of_bounds", ProofLevel::L0Safety, "ay"),
            (VcKind::SliceBoundsCheck, "slice_bounds_check", ProofLevel::L0Safety, "ay"),
            (
                VcKind::Assertion { message: "x != 0".into() },
                "assertion",
                ProofLevel::L0Safety,
                "ay",
            ),
            (
                VcKind::Precondition { callee: "crate::callee".into() },
                "precondition",
                ProofLevel::L1Functional,
                "trust-full-verifier",
            ),
            (
                VcKind::Postcondition,
                "postcondition",
                ProofLevel::L1Functional,
                "trust-full-verifier",
            ),
            (
                VcKind::CastOverflow { from_ty: signed32.clone(), to_ty: unsigned8.clone() },
                "cast_overflow",
                ProofLevel::L0Safety,
                "ay",
            ),
            (
                VcKind::NegationOverflow { ty: signed32.clone() },
                "negation_overflow",
                ProofLevel::L0Safety,
                "ay",
            ),
            (VcKind::Unreachable, "unreachable", ProofLevel::L0Safety, "ay"),
            (VcKind::DeadState { state: "Stuck".into() }, "dead_state", ProofLevel::L2Domain, "ty"),
            (VcKind::Deadlock, "deadlock", ProofLevel::L2Domain, "ty"),
            (
                VcKind::Temporal {
                    property: "□(ready -> safe)".into(),
                    machine: Some(machine.clone()),
                },
                "temporal",
                ProofLevel::L2Domain,
                "ty",
            ),
            (
                VcKind::Liveness {
                    property: LivenessProperty {
                        name: "request_progress".into(),
                        operator: TemporalOperator::LeadsTo,
                        predicate: "requested".into(),
                        consequent: Some("served".into()),
                        fairness: vec![fairness.clone()],
                    },
                    machine: Some(machine),
                },
                "liveness",
                ProofLevel::L2Domain,
                "ty",
            ),
            (VcKind::Fairness { constraint: fairness }, "fairness", ProofLevel::L2Domain, "ty"),
            (
                VcKind::TaintViolation {
                    source_label: "request".into(),
                    sink_kind: "shell".into(),
                    path_length: 3,
                },
                "taint_violation",
                ProofLevel::L1Functional,
                "trust-full-verifier",
            ),
            (
                VcKind::RefinementViolation {
                    spec_file: "service.tla".into(),
                    action: "Commit".into(),
                },
                "refinement_violation",
                ProofLevel::L2Domain,
                "ty",
            ),
            (
                VcKind::ResilienceViolation {
                    service: "db".into(),
                    failure_mode: "timeout".into(),
                    reason: "retry budget exhausted".into(),
                },
                "resilience_violation",
                ProofLevel::L1Functional,
                "trust-full-verifier",
            ),
            (
                VcKind::ProtocolViolation {
                    protocol: "two-phase-commit".into(),
                    violation: "double commit".into(),
                },
                "protocol_violation",
                ProofLevel::L2Domain,
                "ty",
            ),
            (
                VcKind::NonTermination { context: "loop".into(), measure: "remaining".into() },
                "non_termination",
                ProofLevel::L1Functional,
                "trust-full-verifier",
            ),
            (VcKind::FloatDivisionByZero, "float_division_by_zero", ProofLevel::L1Functional, "ay"),
            (
                VcKind::FloatOverflowToInfinity {
                    op: trust_types::BinOp::Mul,
                    operand_ty: signed32,
                },
                "float_overflow_to_infinity",
                ProofLevel::L1Functional,
                "ay",
            ),
            (
                VcKind::UnboundedAllocation {
                    callee: "Vec::with_capacity".into(),
                    count: "n * 2".into(),
                    detail: "count has no established budget".into(),
                },
                "unbounded_allocation",
                ProofLevel::L0Safety,
                "trust-full-verifier",
            ),
            // These families deliberately share the legacy compact `unknown`
            // tag.  The exact typed payload must keep their distinct canonical
            // report kinds, proof levels, and descriptions.
            (
                VcKind::DataRace {
                    variable: "state".into(),
                    thread_a: "writer".into(),
                    thread_b: "reader".into(),
                },
                "data_race",
                ProofLevel::L0Safety,
                "trust-full-verifier",
            ),
            (
                VcKind::FunctionalCorrectness {
                    property: "result_correctness".into(),
                    context: "binary_search postcondition".into(),
                },
                "functional_correctness",
                ProofLevel::L1Functional,
                "trust-full-verifier",
            ),
            (
                VcKind::CopyBoundsViolation {
                    callee: "copy_nonoverlapping".into(),
                    direction: "dst".into(),
                    detail: "count exceeds destination allocation".into(),
                },
                "copy_bounds_violation",
                ProofLevel::L0Safety,
                "trust-full-verifier",
            ),
            (
                VcKind::ExternallyMutableAllocationBounds {
                    allocation_kind: "mmap_file".into(),
                    live_size: "live_file_len".into(),
                    detail: "captured length was not revalidated".into(),
                },
                "externally_mutable_allocation_bounds",
                ProofLevel::L0Safety,
                "trust-full-verifier",
            ),
        ];

        for (index, (kind, expected_tag, expected_level, backend)) in cases.into_iter().enumerate()
        {
            let expected_description = kind.description();
            let result = typed_transport_result(
                &format!("crate::typed_{index}"),
                kind.clone(),
                backend,
                trust_types::Outcome::Unknown,
            );
            assert_eq!(report_vc_kind(&result), kind, "typed family {expected_tag}");

            let canonical = with_live_transport_authority(report_with_result(
                result,
                VerificationOutcome::Unknown,
            ))
            .to_trust_report();
            let obligation = &canonical.functions[0].obligations[0];
            assert_eq!(obligation.kind, expected_tag);
            assert_eq!(obligation.proof_level, expected_level);
            assert_eq!(obligation.description, expected_description);
            assert!(matches!(obligation.outcome, ObligationOutcome::Unknown { .. }));
            assert!(obligation.proof_evidence.is_none());
            assert_eq!(
                obligation
                    .transport_evidence
                    .as_ref()
                    .and_then(|evidence| evidence.typed_kind.as_deref()),
                Some(&kind),
                "canonical transport evidence must retain the exact typed payload for {expected_tag}",
            );
        }
    }

    #[test]
    fn typed_transport_postcond_matches_basic_contract_gate_without_minting_proof() {
        let mut transport = trust_types::TransportObligationResult {
            obligation_id: Some("vc:crate::contract:postcondition:0".into()),
            claim_digest_sha256: Some("a".repeat(64)),
            kind: "postcond".into(),
            typed_kind: Some(Box::new(VcKind::Postcondition)),
            description: "postcondition".into(),
            location: None,
            outcome: trust_types::Outcome::Proved,
            solver: "trust-full-verifier".into(),
            time_ms: 3,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
        };
        let result = transport_to_verification_result("crate::contract", &transport);
        assert_eq!(result.outcome, VerificationOutcome::Proved);
        let canonical = report_with_result(result, VerificationOutcome::Proved).to_trust_report();
        let obligation = &canonical.functions[0].obligations[0];
        assert_eq!(obligation.kind, "postcondition");
        assert_eq!(obligation.proof_level, trust_types::ProofLevel::L1Functional);
        assert_eq!(obligation.description, "postcondition");
        assert!(matches!(obligation.outcome, ObligationOutcome::Unknown { .. }));
        assert!(obligation.proof_evidence.is_none());
        assert_eq!(canonical.summary.total_proved, 0);

        // Even a proof-shaped native row cannot survive a split-brain typed
        // classification. The mismatch is downgraded before live authority can
        // be captured or attached.
        transport = native_full_verifier_transport();
        transport.typed_kind = Some(Box::new(VcKind::DivisionByZero));
        let mismatched = transport_to_verification_result("crate::contract", &transport);
        assert_eq!(mismatched.outcome, VerificationOutcome::Unknown);
        assert!(
            mismatched
                .reason
                .as_deref()
                .is_some_and(|reason| reason.contains("typed VC kind disagrees"))
        );
        assert!(matches!(report_vc_kind(&mismatched), VcKind::UnsupportedMir { .. }));
    }

    #[test]
    fn obligation_id_cannot_retype_exact_assertion_as_postcondition() {
        let kind = VcKind::Assertion { message: "source assertion".into() };
        let transport = trust_types::TransportObligationResult {
            obligation_id: Some("vc:crate::contract:postcondition:0".into()),
            claim_digest_sha256: Some("a".repeat(64)),
            kind: kind.transport_tag(),
            typed_kind: Some(Box::new(kind.clone())),
            description: kind.description(),
            location: None,
            outcome: trust_types::Outcome::Unknown,
            solver: "trust-full-verifier".into(),
            time_ms: 3,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
        };
        let result = transport_to_verification_result("crate::contract", &transport);
        assert_eq!(report_vc_kind(&result), kind);

        let canonical = report_with_result(result, VerificationOutcome::Unknown).to_trust_report();
        let obligation = &canonical.functions[0].obligations[0];
        assert_eq!(obligation.kind, "assertion");
        assert_eq!(obligation.proof_level, trust_types::ProofLevel::L0Safety);
        assert_ne!(obligation.kind, "postcondition");
    }

    #[test]
    fn obligation_id_cannot_repair_missing_full_verifier_typed_kind() {
        let fieldful_kind = VcKind::Temporal { property: "□ safe".into(), machine: None };
        let mut transport = native_full_verifier_transport();
        transport.obligation_id = Some("vc:crate::contract:postcondition:0".into());
        transport.kind = fieldful_kind.transport_tag();
        transport.description = fieldful_kind.description();
        transport.typed_kind = None;
        transport.outcome = trust_types::Outcome::Unknown;
        transport.native_trust_ir = None;
        transport.proof_evidence = None;
        let result = transport_to_verification_result("crate::contract", &transport);

        assert!(matches!(report_vc_kind(&result), VcKind::UnsupportedMir { .. }));
        let canonical = report_with_result(result, VerificationOutcome::Unknown).to_trust_report();
        let obligation = &canonical.functions[0].obligations[0];
        assert_eq!(obligation.kind, "unsupported_mir");
        assert_ne!(obligation.kind, "postcondition");
        assert!(matches!(obligation.outcome, ObligationOutcome::Unknown { .. }));
    }

    #[test]
    fn authenticated_typed_timeout_remains_a_timeout() {
        let result = typed_transport_result(
            "crate::timed",
            VcKind::Postcondition,
            "trust-full-verifier",
            trust_types::Outcome::Timeout,
        );
        assert_eq!(result.outcome, VerificationOutcome::Timeout);
        let canonical =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Timeout))
                .to_trust_report();
        assert!(matches!(
            canonical.functions[0].obligations[0].outcome,
            ObligationOutcome::Timeout { timeout_ms: 17 }
        ));
    }

    // Trust (green front door, W0.1): an `assumption:<tag>` row must NEVER be
    // laundered into a runtime-checked obligation. It has nothing enforced at
    // runtime; folding it to Assertion gave it a runtime fallback so
    // RuntimeCheckPolicy::Auto relabeled it RuntimeChecked in report.json (a
    // live lie on async-coroutine libs). It must stay Unknown/Inconclusive.
    #[test]
    fn assumption_row_never_renders_as_runtime_checked() {
        let assumption = VerificationResult {
            function: "crate::tick::{closure#0}".into(),
            kind: "assumption:coroutine".into(),
            message: "unverified assumption: MIR shape the verifier cannot lower yet (coroutine)"
                .into(),
            outcome: VerificationOutcome::Unknown,
            backend: "trust-classifier".into(),
            time_ms: Some(0),
            location: None,
            counterexample: None,
            reason: Some("verifier capability gap `coroutine`".into()),
            raw_line: String::new(),
        };
        let report = report_with_results_and_diagnostics(vec![assumption], Vec::new());
        let trust_report = report.to_trust_report();

        assert_eq!(
            trust_report.summary.total_runtime_checked, 0,
            "assumption rows must not be counted as runtime-checked"
        );
        assert_eq!(trust_report.summary.total_unknown, 1);
        assert_ne!(trust_report.summary.verdict, trust_types::CrateVerdict::RuntimeChecked);
        assert!(
            matches!(
                trust_report.functions[0].obligations[0].outcome,
                ObligationOutcome::Unknown { .. }
            ),
            "an assumption row must render Unknown, got {:?}",
            trust_report.functions[0].obligations[0].outcome
        );
    }

    #[test]
    fn authenticated_zero_obligation_functions_remain_typed_without_proof_credit() {
        let inventory = VerificationResult {
            function: "crate::empty".into(),
            kind: "no_obligations".into(),
            message: "function has no panic obligations (trivially panic-free)".into(),
            outcome: VerificationOutcome::Proved,
            backend: "trust-structural".into(),
            time_ms: Some(0),
            location: None,
            counterexample: None,
            reason: Some("verified: zero panic obligations".into()),
            raw_line: String::new(),
        };
        let mut report = report_with_results_and_diagnostics(vec![inventory], Vec::new());
        report.coverage = Some(trust_types::VerificationCoverage::from_counts(1, 1));
        let report = with_live_transport_authority(report);

        assert!(report.results.is_empty());
        assert_eq!(report.zero_obligation_functions, ["crate::empty"]);
        assert!(report.success, "complete exact inventory may pass the run gate");

        let canonical = report.to_trust_report();
        assert_eq!(canonical.functions.len(), 1);
        assert_eq!(canonical.functions[0].function, "crate::empty");
        assert!(canonical.functions[0].obligations.is_empty());
        assert_eq!(canonical.functions[0].summary.verdict, FunctionVerdict::NoObligations);
        assert_eq!(canonical.summary.functions_analyzed, 1);
        assert_eq!(canonical.summary.functions_verified, 0);
        assert_eq!(canonical.summary.total_obligations, 0);
        assert_eq!(canonical.summary.total_proved, 0);
        assert_eq!(canonical.summary.verdict, trust_types::CrateVerdict::NoObligations);
    }

    // Trust (green front door, W0.2): a nonzero build exit means the crate did
    // not verify — rows collected before the abort must never render Verified.
    #[test]
    fn nonzero_exit_caps_verdict_below_verified() {
        // A run that hard-aborted after collecting only proved rows (live bug:
        // a format! lib reported Verified 3/3 while exiting 101).
        let proved = VerificationResult {
            function: "crate::greet".into(),
            kind: "no_obligations".into(),
            message: "function has no panic obligations".into(),
            outcome: VerificationOutcome::Proved,
            backend: "trust-structural".into(),
            time_ms: Some(0),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        };
        let mut report = report_with_results_and_diagnostics(vec![proved], Vec::new());
        report.exit_code = 101;
        report.success = false;
        let trust_report = report.to_trust_report();

        assert_ne!(
            trust_report.summary.verdict,
            trust_types::CrateVerdict::Verified,
            "a nonzero-exit run must never render Verified"
        );
        assert_eq!(trust_report.summary.verdict, trust_types::CrateVerdict::Inconclusive);
    }
}
