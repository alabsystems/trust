// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-08-21; do not grow casually
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

mod source_clause;

/// Borrowed compiler observations published beside the sealed proof report.
#[derive(Default)]
pub(crate) struct CompilerResourceReports<'a> {
    pub(crate) memory: Option<&'a [crate::compiler_memory::CompilerMemoryObservation]>,
    pub(crate) admission: Option<&'a crate::compiler_admission::Report>,
}

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
/// Aggregate bytes `--report-dir` may COPY into the bundle's own artifact
/// store. A memory/disk guard on a second copy of bytes this run produced, not
/// a trust boundary: every artifact is re-hashed on decode and a saved report
/// never carries proof authority (`diff::load_report` downgrades it). Since
/// 2026-10-01 an artifact whose copy would cross it is OMITTED — recorded in
/// [`REPORT_EVIDENCE_BUNDLE_FILE`] — instead of discarding the whole verdict;
/// see [`persist_report_artifact_store`].
const MAX_REPORT_ARTIFACT_STORE_BYTES: u64 = 512 * 1024 * 1024;
/// Machine-readable completeness record written into every report bundle.
/// `report.json` itself is fixed by the publication seal and cannot say that
/// part of its evidence was not persisted, so this sidecar does.
const REPORT_EVIDENCE_BUNDLE_FILE: &str = "evidence-bundle.json";
const REPORT_EVIDENCE_BUNDLE_SCHEMA: &str = "trust.report-evidence-bundle.v1";
// Decision (2026-09-18): the inline evidence cap is unified with the store
// cap above. A refused seal never reaches the render/store lane (see the refusal
// note ~L3921), so the store cap could not relieve inline pressure — a strict
// proof that a body is panic-free simply could not seal once its bit-level
// evidence crossed 48 MiB, which the widened bit-vector proof machinery pushed
// the largest constant-scaled byte assemblers (`trust-endian` `u64_be`,
// `trust-radix64`) over. The evidence has ALSO been shrunk at the source — the
// trust-mc translator now lowers constant-factor overflow checks to native-width
// comparisons and constant power-of-two multiplies to shifts — which reseals the
// smaller composers; this lifts the transport ceiling for the rest. Inline
// evidence is a self-contained proof, no less bounded than the store lane that
// already accepts this size, so the two caps are one number.
//
// FLOOR for the inlined-evidence ceiling, in DECODED bytes. The bound actually
// applied is [`max_inline_report_artifact_bytes`], which is charged in hex, so
// its floor is twice this number.
const MAX_INLINE_REPORT_ARTIFACT_BYTES: u64 = MAX_REPORT_ARTIFACT_STORE_BYTES;

/// How much proof evidence one sealed report may inline, scaled to the machine
/// and never below the flat floor.
///
/// A sealed publication capability cannot hold pathnames, so the seal decodes
/// every artifact beneath the run's root and binds the bytes. That made the
/// flat 48 MiB then in force (512 MiB decoded since the 2026-09-18
/// decision above, which — expressed in hex — is now this function's floor) a
/// cap on the SIZE OF THE RUN:
/// proof-artifact roots from this week measure 25, 114, 130, 385 and 408 MiB,
/// and every one of the larger ones refused to seal after the verification had
/// already been paid for. The bytes are ones this run just produced, each
/// checked against its declared sha256 on decode, so this is a memory guard
/// rather than a trust boundary — the same reasoning, and the same
/// eighth-of-memory rule, that `max_authenticated_cargo_transport_bytes`
/// already applies one layer down.
fn max_inline_report_artifact_bytes() -> u64 {
    #[cfg(test)]
    if let Some(budget) = test_hooks::INLINE_BUDGET_BYTES.with(std::cell::Cell::get) {
        return budget;
    }
    // Bounded by what a READER may load, not by what this process may emit.
    //
    // Scaling this with the emit ceiling made it 4 GiB on a 128 GiB machine,
    // which bounds nothing: a report that large is refused by the emit check
    // anyway, and is unreadable regardless, because every consumer of a saved
    // report slurps it whole under MAX_SAVED_PROOF_REPORT_BYTES (128 MiB when
    // this was written; 512 MiB since the 2026-09-18 decision).
    // Inlined evidence therefore gets at most HALF of a reader's budget, so a
    // report whose artifacts fit stays self-contained and still leaves room for
    // the obligations themselves — which were the other 42% of the one report
    // measured end to end.
    //
    // The 2026-09-18 decision (above) capped inline evidence at
    // 512 MiB of DECODED bytes. This budget is charged ENCODED — every
    // inlined artifact is stored as hex, two characters per byte (see
    // `inline_artifact_materializations`) — so the floor is that decoded cap
    // expressed in hex: 2 x 512 MiB = 1 GiB of hex, exactly 512 MiB decoded.
    // The floor, not the reader half (256 MiB of hex), is what applies today,
    // and the budget is therefore never tighter than the owner's cap. What
    // changed is only what happens past it — the artifact stays in the store
    // instead of the whole seal being refused.
    //
    // Artifacts past this budget are not lost and not refused: they stay
    // content-addressed at `<store>/sha256/<digest>`, and the digest that
    // names them is bound by the seal.
    let reader_half = (crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES / 2) as u64;
    reader_half.max(MAX_INLINE_REPORT_ARTIFACT_BYTES.saturating_mul(2))
}

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

/// Serialize into a SHA-256 digest without ever holding the bytes.
///
/// The publication state's serialization is used for exactly ONE thing: the
/// `complete_report_receipt` hash. It is never inspected. Materializing it was
/// therefore pure peak memory, paid once per `complete_authorized_rows()` call
/// — and there are six call sites, each allocating the whole state again.
///
/// MEASURED on ay 2026-09-15: `targo-trust` went 17.0 GB -> 49.5 GB -> 58.2 GB
/// in ninety seconds during report assembly and was SIGKILLed (rc=137), after
/// four and a half hours of verification that had already succeeded.
struct HashingWriter<'a> {
    digest: &'a mut Sha256,
}

impl Write for HashingWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.digest.update(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// Counts serialized bytes, refusing past `limit`, without retaining them.
///
/// The digest frame commits to each part's LENGTH before its bytes, so the
/// length has to be known first. Counting is a second serialization pass, which
/// costs CPU and no memory — the trade this whole change exists to make.
struct CountingWriter {
    len: u64,
    limit: u64,
}

impl Write for CountingWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let next = self.len.saturating_add(bytes.len() as u64);
        if next > self.limit {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("canonical report exceeds the {}-byte saved-report limit", self.limit),
            ));
        }
        self.len = next;
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub(crate) fn serialize_json_bounded(value: &impl Serialize, limit: usize) -> io::Result<Vec<u8>> {
    let mut output = BoundedReportBytes { bytes: Vec::new(), limit };
    serde_json::to_writer(&mut output, value)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    Ok(output.bytes)
}

fn serialize_canonical_report_bounded(
    report: &trust_types::JsonProofReport,
) -> io::Result<Vec<u8>> {
    serialize_json_bounded(report, crate::input_limits::max_emitted_proof_report_bytes())
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
    /// Every bound the run was held to, as the compiler received it
    /// (determinism plan §3.6): the workspace root's `[trust]` budgets and
    /// the run's `--worker-threads`.
    pub(crate) budget_profile: trust_types::determinism::BudgetProfile,
    pub(crate) enabled: bool,
    pub(crate) hardened: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) trust_profile: Option<String>,
    /// The Trust requirements Cargo project configuration supplied and this
    /// run adopted (`targo config trust-policy`), when it set any. Printed in
    /// the report header; published as `verification_gate.project_requirements`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) project_requirements: Option<trust_types::ProjectRequirementsReport>,
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
    /// Trust (CB4): authenticated bodies the compiler EXCLUDED from the proof
    /// inventory because rustc's libtest harness synthesized them — one entry
    /// per exact exclusion row, sorted by function
    /// (`crate::types::authenticated_test_harness_exclusions`). Inventory like
    /// `zero_obligation_functions`: the rows are elided from `results`, never
    /// counted in `total`, never proof. Bound by the live authority exactly as
    /// the zero-obligation inventory is. Empty (and omitted) outside a
    /// test-harness build.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) test_harness_exclusions: Vec<trust_types::GateExclusionReport>,
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
    /// Coverage rows the compiler emitted that this run DROPPED (advisory lanes
    /// only; strict refuses the run instead), each with the defect that dropped
    /// it (`ParsedCompilerOutput::dropped_coverage`). Read by `coverage_line`, so
    /// a dropped row is never reported as an absent one.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) coverage_dropped: Vec<String>,
    /// Determinism plan §2: the backstops (and unexplained stops) the
    /// compilers' backstop ledgers saw fire anywhere in the run — including in
    /// work consumed without publishing a row, such as the R1 harvest, a
    /// refutation attempt or S1 revalidation — merged from every unit's
    /// `coverage_summary` transport. Any entry keeps the run from being
    /// `measured` ([`crate::determinism_report::UnitDeterminism::of_rows`]).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) noted_stops: Vec<trust_types::determinism::NotedStop>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) test_execution: Option<CertifiedTestExecutionReport>,
    /// Observational projection of Cargo's exact declared proof frontier and
    /// the units that completed and emitted coverage. Populated only for Cargo
    /// crate-mode runs and never used as live proof authority.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) cargo_proof_inventory: Option<trust_types::CargoProofInventoryReport>,
    /// Trust (#220 — publication boundary): what the one publication
    /// normalization withheld from this report, counted by that pass itself
    /// (`crate::types::normalize_authenticated_results_for_publication`).
    ///
    /// `docs/TCB.md`'s "The publication boundary" section documents the rule:
    /// `targo trust` applies a second evidence test after the compiler's verdict
    /// vector and rewrites every favorable row that carries neither a
    /// clean-kernel certificate nor publishable native evidence. `--json`
    /// discloses the relabelled rows per row; the ones the alias-elision passes
    /// then elide need separate diagnostic disclosure. This field retains their
    /// identities for stderr without changing the canonical proof vector.
    ///
    /// `None` means the report was not built from an authenticated compiler
    /// vector (internal gate probes and test fixtures). The terminal says so
    /// rather than printing a zero — "0 withheld" and "not measured" are
    /// different claims.
    ///
    /// Deliberately `#[serde(skip)]`: this is additive disclosure, and the
    /// canonical sealed JSON report must be byte-identical to what it was.
    #[serde(skip)]
    pub(crate) publication_boundary: Option<crate::types::PublicationBoundary>,
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
    /// How many proof artifacts the seal left in the content-addressed store
    /// instead of inlining, because inlining them would have crossed the
    /// budget. Non-zero means the private artifact root must stay alive
    /// through credit evaluation: those artifacts are resolved by re-reading
    /// and re-hashing the file, and with no root they would silently earn no
    /// credit at all. Runtime state; never serialized.
    pub(crate) still_path_backed_artifacts: usize,
    report_subject: String,
    verification_session: String,
    row_receipts: Vec<[u8; 32]>,
    zero_obligation_functions: Vec<String>,
    /// Trust (CB4): the exact test-harness exclusion inventory derived from the
    /// authenticated rows, bound exactly like `zero_obligation_functions`.
    test_harness_exclusions: Vec<trust_types::GateExclusionReport>,
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

/// `serde_json::to_vec(expected) == serde_json::to_vec(actual)` for two row
/// vectors, decided WITHOUT materializing either whole-vector serialization.
///
/// `serde_json` frames a sequence as `[`, the elements' own bytes joined by
/// `,`, then `]` — no separator or framing byte depends on an element's
/// contents. The two whole-vector buffers are therefore equal exactly when the
/// vectors have the same length and every corresponding pair of rows
/// serializes to the same bytes, which is what this decides, one row at a time
/// into two reused buffers. The comparison is the SAME comparison; only its
/// peak footprint changes, from two whole serialized reports to two rows.
///
/// `None` propagates a serialization failure, exactly as the `.ok()?` on the
/// whole-vector form did: a sequence serialization fails precisely when one of
/// its elements fails, and the caller returns `None` for a failure and for a
/// mismatch alike.
fn publication_projection_is_byte_identical(
    expected: &[VerificationResult],
    actual: &[VerificationResult],
) -> Option<bool> {
    if expected.len() != actual.len() {
        return Some(false);
    }
    let mut expected_row_bytes: Vec<u8> = Vec::new();
    let mut actual_row_bytes: Vec<u8> = Vec::new();
    for (expected_row, actual_row) in expected.iter().zip(actual.iter()) {
        expected_row_bytes.clear();
        actual_row_bytes.clear();
        serde_json::to_writer(&mut expected_row_bytes, expected_row).ok()?;
        serde_json::to_writer(&mut actual_row_bytes, actual_row).ok()?;
        if expected_row_bytes != actual_row_bytes {
            return Some(false);
        }
    }
    Some(true)
}

impl LiveTransportAuthority {
    /// Takes the authenticated compiler vector BY VALUE.
    ///
    /// The drift check this constructor performs is unchanged: it rederives the
    /// publication projection from the exact authenticated rows and compares it
    /// byte-for-byte against the caller's `publication_results`. What changed is
    /// where that rederivation is computed. It used to be computed in a THIRD
    /// full row vector (`authenticated_compiler_results.to_vec()`) that was live
    /// alongside both the caller's authenticated snapshot and the caller's
    /// publication vector. Every caller's last use of the authenticated vector
    /// is this call, so the vector is consumed here and the projection is
    /// computed IN it instead. The comparison still runs against a vector that
    /// was derived independently of `publication_results`, so a post-parse
    /// rewrite of the caller's rows still fails it — a borrow of the caller's
    /// publication vector would compare a thing against itself, and that is
    /// exactly what is NOT done here.
    pub(crate) fn capture_authenticated_projection(
        report_subject: &str,
        verification_session: &str,
        authenticated_compiler_results: Vec<VerificationResult>,
        publication_results: &[VerificationResult],
        materialization_root: Option<&Path>,
        test_target_panics: crate::test_target_panics::TestTargetPanicPolicy,
    ) -> Option<Self> {
        // Derived from the EXACT authenticated rows, before the projection
        // below rewrites them in place. This is a pure function of those rows,
        // so hoisting it above the byte comparison changes its value not at
        // all; it is hoisted only so the authenticated vector itself can serve
        // as the projection buffer. On the comparison-failure path it is now
        // computed and discarded, which costs a sort of the zero-obligation
        // function names on a run that is about to fail closed anyway.
        let zero_obligation_functions =
            crate::types::authenticated_zero_obligation_inventory(&authenticated_compiler_results);
        // Trust (CB4): the same derivation for the libtest harness exclusions,
        // which the projection below elides exactly as it elides the
        // zero-obligation rows.
        let test_harness_exclusions =
            crate::types::authenticated_test_harness_exclusions(&authenticated_compiler_results);
        let mut expected_publication = authenticated_compiler_results;
        crate::types::normalize_authenticated_results_for_publication(
            &mut expected_publication,
            materialization_root,
        );
        // The caller's explicit `--test-target-panics` policy is part of the
        // publication projection, so it is REDERIVED here from the exact
        // compiler vector rather than accepted from the caller's rows. A
        // hand-edited outcome therefore still fails the byte comparison below,
        // exactly as it did before the flag existed; under the default
        // `Strict` this call is a no-op and the comparison is unchanged.
        crate::test_target_panics::apply(&mut expected_publication, test_target_panics);
        if !publication_projection_is_byte_identical(&expected_publication, publication_results)? {
            return None;
        }
        // The projection has served its only purpose. Release it before the row
        // receipts below allocate, rather than at the end of the function.
        drop(expected_publication);
        if publication_results
            .iter()
            .any(|result| zero_obligation_functions.binary_search(&result.function).is_ok())
        {
            return None;
        }
        // Trust (CB4): an excluded body is excluded WHOLE. The compiler writes
        // exactly one row for it, so a published row that still names an excluded
        // function means the exclusion shared its envelope with something else;
        // refuse authority rather than let an exclusion hide a sibling row.
        if publication_results.iter().any(|result| {
            test_harness_exclusions
                .binary_search_by(|exclusion| exclusion.function.as_str().cmp(&result.function))
                .is_ok()
        }) {
            return None;
        }
        Self::capture_exact(
            report_subject,
            verification_session,
            publication_results,
            zero_obligation_functions,
            test_harness_exclusions,
        )
    }

    fn capture_exact(
        report_subject: &str,
        verification_session: &str,
        results: &[VerificationResult],
        zero_obligation_functions: Vec<String>,
        test_harness_exclusions: Vec<trust_types::GateExclusionReport>,
    ) -> Option<Self> {
        if report_subject.trim().is_empty()
            || !trust_types::digest::is_stable_sha256_hex(verification_session)
        {
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
            test_harness_exclusions,
            still_path_backed_artifacts: 0,
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
    ) -> Result<(), String> {
        if self.validate_rows(report_subject, results).is_none() {
            return Err("the row receipts no longer authorize the report's own rows: the \
                        subject, the session digest, or the receipt count disagrees"
                .to_string());
        }

        let mut inlined = results.to_vec();
        let still_path_backed =
            match inline_verification_result_artifacts(&mut inlined, artifact_root) {
                Ok(count) => count,
                Err(error) => {
                    return Err(format!(
                        "a path-backed proof materialization did not decode against its \
                         declared digest: {error}"
                    ));
                }
            };
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
            return Err("a row receipt could not be minted over the inlined rows".to_string());
        };

        // SWAP, not clone. `inlined` is a full copy of every row INCLUDING the
        // freshly inlined artifact bytes, and it dies at the end of this
        // function; cloning it back made the largest thing in the process exist
        // three times at once (original + inlined + the copy). Swapping hands
        // the rows over and leaves the old ones in `inlined` to be dropped.
        // Lengths are equal by construction (`inlined` came from `to_vec`).
        results.swap_with_slice(&mut inlined);
        self.still_path_backed_artifacts = still_path_backed;
        self.row_receipts = row_receipts;
        self.complete_report_receipt = None;
        self.canonical_report_receipt = None;
        self.sealed_canonical_report = None;
        self.sealed_canonical_bytes = None;
        Ok(())
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
        test_harness_exclusions: &[trust_types::GateExclusionReport],
        serialized_report: [u8; 32],
        artifact_root: Option<&Path>,
    ) -> bool {
        let _ = artifact_root;
        if self.validate_rows(report_subject, results).is_none()
            || self.zero_obligation_functions != zero_obligation_functions
            || self.test_harness_exclusions != test_harness_exclusions
        {
            return false;
        }
        // The receipt arrives already computed, by streaming the state through
        // the hasher rather than materializing it. `complete_report_receipt`
        // remains the definition of the frame; `streamed_complete_report_receipt`
        // feeds it exactly the same bytes in the same order.
        if self.complete_report_receipt != Some(serialized_report) {
            // Execution outcomes can change after proof qualification. A new
            // complete-state receipt must rebuild its canonical projection;
            // the old DTO is bound to the preceding gate and test outcome.
            self.canonical_report_receipt = None;
            self.sealed_canonical_report = None;
            self.sealed_canonical_bytes = None;
        }
        self.complete_report_receipt = Some(serialized_report);
        true
    }

    fn validate_complete_report<'a>(
        &'a self,
        report_subject: &str,
        results: &'a [VerificationResult],
        zero_obligation_functions: &[String],
        test_harness_exclusions: &[trust_types::GateExclusionReport],
        serialized_report: [u8; 32],
        artifact_root: Option<&Path>,
    ) -> Option<AuthorizedRows<'a>> {
        let _ = artifact_root;
        let rows = self.validate_rows(report_subject, results)?;
        if self.zero_obligation_functions != zero_obligation_functions
            || self.test_harness_exclusions != test_harness_exclusions
        {
            return None;
        }
        let expected = self.complete_report_receipt?;
        (serialized_report == expected).then_some(rows)
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

    /// Re-mint row authority over a vector in which NOTHING is claimed proved.
    ///
    /// This is the ONLY path that re-captures authority after the original
    /// mint, and it is deliberately incapable of granting credit: it refuses
    /// unless every row is non-favorable, so the re-minted receipts can
    /// authorize no proved row at all (`authorizes_proved_row` requires
    /// `outcome.is_proved()`). A fail-closed publication may therefore be
    /// sealed without the seal ever accepting evidence it refused.
    fn recapture_over_unproved_rows(
        &self,
        report_subject: &str,
        results: &[VerificationResult],
        zero_obligation_functions: Vec<String>,
        test_harness_exclusions: Vec<trust_types::GateExclusionReport>,
    ) -> Option<Self> {
        if results.iter().any(|result| {
            matches!(
                result.outcome,
                VerificationOutcome::Proved | VerificationOutcome::RuntimeChecked
            )
        }) {
            return None;
        }
        Self::capture_exact(
            report_subject,
            &self.verification_session,
            results,
            zero_obligation_functions,
            test_harness_exclusions,
        )
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

/// The same receipt as [`complete_report_receipt`], computed without ever
/// holding the serialized state.
///
/// Byte-identical by construction: the frame below feeds exactly the bytes
/// `length_bound_sha256` would, in the same order, with the same lengths — the
/// state's bytes simply arrive through the hasher instead of through a Vec.
/// `Err` means the state crossed the emit bound, which is what the
/// materializing path reported too.
fn streamed_complete_report_receipt(
    report_subject: &str,
    verification_session: &str,
    state: &impl Serialize,
    artifact_root: Option<&Path>,
    limit: u64,
) -> io::Result<[u8; 32]> {
    // Pass one: the length, which the frame commits to before the bytes.
    let mut counter = CountingWriter { len: 0, limit };
    serde_json::to_writer(&mut counter, state)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    let serialized_len = counter.len;

    let artifact_root = artifact_root
        .map_or_else(Vec::new, |path| path.as_os_str().to_string_lossy().as_bytes().to_vec());
    let domain = "targo.complete-publication-state.v1";

    let mut digest = Sha256::new();
    digest.update(b"targo.digest-frame.v1");
    digest.update((domain.len() as u64).to_be_bytes());
    digest.update(domain.as_bytes());
    digest.update((4_u64).to_be_bytes());
    digest.update((report_subject.len() as u64).to_be_bytes());
    digest.update(report_subject.as_bytes());
    digest.update((verification_session.len() as u64).to_be_bytes());
    digest.update(verification_session.as_bytes());
    digest.update(serialized_len.to_be_bytes());
    // Pass two: the bytes themselves, straight into the digest.
    serde_json::to_writer(&mut HashingWriter { digest: &mut digest }, state)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    digest.update((artifact_root.len() as u64).to_be_bytes());
    digest.update(&artifact_root);
    Ok(digest.finalize().into())
}

/// The materializing definition of the frame [`streamed_complete_report_receipt`]
/// feeds. Production no longer calls it; it is kept as the test oracle that pins
/// the streamed receipt to it byte for byte.
#[cfg(test)]
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
    /// T9: the compact per-obligation records of the same final rows, when
    /// the run attached them (`crate::obligations`).
    obligations: Option<crate::obligations::ObligationRecords>,
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
    /// Attach the compact per-obligation records of the rows this report
    /// seals (T9).
    pub(crate) fn with_obligations(
        mut self,
        records: crate::obligations::ObligationRecords,
    ) -> Self {
        self.obligations = Some(records);
        self
    }

    /// The compact per-obligation records of this run, for the committed
    /// baseline and `targo trust diff --baseline`.
    pub(crate) fn obligation_records(&self) -> Option<&crate::obligations::ObligationRecords> {
        self.obligations.as_ref()
    }

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

    /// Canonical rows for `targo trust spec`'s failing-run disclosure. The
    /// spec surface suppresses ordinary report rendering (no report artifacts
    /// were requested), so on a failing verified run it reads the sealed rows
    /// here to say WHY — a non-zero exit with no visible cause is the
    /// fail-silent defect class, not a rendering choice.
    pub(crate) fn for_spec_gate_disclosure(&self) -> &trust_types::JsonProofReport {
        &self.report
    }
}

/// Why the final publication seal refused.
///
/// The seal is the last gate before any verdict is printed, so a refusal here
/// silences the WHOLE run. Naming the precondition is what lets the caller
/// publish an honest no-verdict disclosure instead of exiting 2 with nothing,
/// and lets a reader tell a refused SEAL from a refuted OBLIGATION.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SealRefusal {
    /// No live compiler-transport authority to seal against.
    MissingLiveTransportAuthority,
    /// Inlining the captured root failed. The payload names WHICH of the three
    /// unrelated steps refused — row authorization, artifact decoding, or
    /// receipt minting — because pooling them behind one message misattributes
    /// two of them as a digest mismatch that never happened.
    ArtifactInliningRejected(String),
    /// The internal publication state could not be serialized within bounds.
    PublicationStateUnserializable,
    /// The complete-report receipt did not bind the exact row vector.
    CompleteReportReceiptRejected,
    /// The canonical projection users see disagrees with the internal state.
    CanonicalProjectionDiverged(String),
    /// The canonical report could not be serialized within bounds.
    CanonicalReportUnserializable,
    /// The canonical-projection receipt refused to bind.
    CanonicalReceiptRejected,
}

impl SealRefusal {
    /// The exact precondition that failed.
    pub(crate) fn precondition(&self) -> String {
        match self {
            Self::MissingLiveTransportAuthority => {
                "no live compiler-transport authority was minted for this run".to_string()
            }
            Self::ArtifactInliningRejected(detail) => detail.clone(),
            Self::PublicationStateUnserializable => {
                "the run's publication state exceeded the bounded serialization limit".to_string()
            }
            Self::CompleteReportReceiptRejected => {
                "the complete-report receipt no longer binds the exact compiler row vector"
                    .to_string()
            }
            Self::CanonicalProjectionDiverged(detail) => detail.clone(),
            Self::CanonicalReportUnserializable => {
                "the canonical report exceeded the bounded serialization limit".to_string()
            }
            Self::CanonicalReceiptRejected => {
                "the canonical-projection receipt refused to bind the sealed report".to_string()
            }
        }
    }
}

impl std::fmt::Display for SealRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.precondition())
    }
}

impl VerificationReport {
    /// Match the opaque same-process producer identity. A saved report cannot
    /// recreate this authority or qualify another run's executable inventory.
    pub(crate) fn authenticates_verification_session(&self, session: &str) -> bool {
        self.live_transport_authority
            .as_ref()
            .is_some_and(|authority| authority.verification_session == session)
    }

    /// Determinism accounting over the published rows (plan
    /// `docs/design/2026-09-29-incremental-deterministic-trust-results.md`
    /// §3.7): the stop cause of every obligation, the unit outcome and the
    /// verdict vector.
    pub(crate) fn determinism(&self) -> crate::determinism_report::UnitDeterminism {
        crate::determinism_report::UnitDeterminism::of_rows(&self.results, &self.noted_stops)
    }

    /// Record the determinism block on the verification gate. Call it once the
    /// rows are final and before the publication seal, which covers the gate.
    pub(crate) fn install_gate(&mut self, mut gate: trust_types::VerificationGateReport) {
        // The published record of what Cargo project configuration required
        // and this run adopted (`verification_gate.project_requirements` in
        // report.json, NDJSON, `--format json` and HTML). Installed with the
        // gate, before the publication seal, which covers the gate.
        gate.project_requirements = self.config.project_requirements.clone();
        self.gate = Some(gate);
    }

    pub(crate) fn record_determinism(&mut self) {
        let block = self.determinism().gate_block(&self.config.budget_profile);
        let failure_sites = self.failure_sites();
        if let Some(gate) = self.gate.as_mut() {
            gate.determinism = Some(block);
            // Recomputed with the determinism block, from the same final rows,
            // so every regrade that re-records one re-records the other.
            gate.failure_sites = Some(failure_sites);
        }
    }

    /// Distinct-site accounting over the rows the gate counts `failed`
    /// (`trust_types::failure_sites`): a MIR assert refuted under the hardened
    /// profile is TWO failed rows — the L0 overflow/bounds row and its
    /// `hardened_panic_boundary` twin — at ONE site. Both rows stay failed and
    /// `counts.failed` is unchanged; this only links them and counts sites.
    /// Every row is passed (pairing ambiguity depends on the rows that did not
    /// fail too); twin classification is `panic_twin_pairing`, the classifier
    /// the subsumption pass uses. It grants nothing.
    pub(crate) fn failure_sites(&self) -> trust_types::failure_sites::FailureSiteAccounting {
        let rows: Vec<(&VerificationResult, VcKind, Option<String>)> = self
            .results
            .iter()
            .map(|row| {
                let id = structured_transport_evidence(row).and_then(|e| e.obligation_id);
                (row, report_vc_kind(row), id)
            })
            .collect();
        trust_types::failure_sites::account_failure_sites(rows.iter().map(|(row, kind, id)| {
            trust_types::failure_sites::SiteRowView {
                function: &row.function,
                obligation_id: id.as_deref(),
                kind,
                location: row.location.as_ref(),
                failed: crate::pipeline::hardened::counts_as_failed(row),
                twin_pairing: crate::types::panic_twin_pairing(row),
            }
        }))
    }

    /// Seal the final run-level publication state after outcome, coverage,
    /// hardened, missing-transport, gate, and exit decisions are fixed.  Row
    /// receipts alone are intentionally insufficient for a crate-level
    /// Verified/PASS claim.
    #[cfg(test)]
    pub(crate) fn seal_for_publication(&mut self) -> bool {
        self.seal_publication_state().is_ok()
    }

    /// The same seal, with the refused PRECONDITION named.
    ///
    /// A bare `false` used to end the run at exit 2 having published nothing —
    /// no `Summary:`, no `Gate:`, no coverage row. A downstream gate reading
    /// only the exit status then cannot tell a no-verdict run from a
    /// refutation, which is the dangerous shape: measured 2026-09-15, one of
    /// the nineteen strict crate gates read that bare nonzero exit as "the
    /// strict lane REFUTED a byte-order swap" when in fact nothing had been
    /// verified at all. Every refusal now names its precondition and the fix
    /// options (DESIGN_PHILOSOPHY principle 10, ruling v7/D3).
    pub(crate) fn seal_publication_state(&mut self) -> Result<(), SealRefusal> {
        // Pathnames are mutable ambient state and cannot survive inside a
        // final publication capability. Validate the old row receipts, then
        // transactionally decode every materialization beneath the captured
        // root against its declared digest and rebind only those exact bytes.
        if let Some(artifact_root) = self.proof_artifact_root.clone() {
            let Some(authority) = self.live_transport_authority.as_mut() else {
                return Err(SealRefusal::MissingLiveTransportAuthority);
            };
            if let Err(detail) = authority.inline_authenticated_rows(
                &self.report_subject,
                &mut self.results,
                &artifact_root,
            ) {
                return Err(SealRefusal::ArtifactInliningRejected(detail));
            }
            // Release the root ONLY when inlining consumed every artifact.
            //
            // Clearing it unconditionally was correct while inlining was
            // all-or-nothing. It is not once the budget leaves artifacts in the
            // content-addressed store: EVERY credit predicate resolves such an
            // artifact by re-reading and re-hashing the file through this root
            // (`matches_sha256_digest_at_root` -> `securely_read_materialized_path`),
            // and `to_trust_report()` — which is what mints proof credit — runs
            // BELOW this point. With no root those artifacts silently earn no
            // credit, so a report would lose proofs it had actually established:
            // a verification downgrade disguised as a size fix.
            //
            // The root is `#[serde(skip)]` runtime authority, so holding it
            // through evaluation puts no pathname inside the sealed capability,
            // which is what the rule above actually forbids.
            let remaining = self
                .live_transport_authority
                .as_ref()
                .map_or(0, |authority| authority.still_path_backed_artifacts);
            if remaining == 0 {
                self.proof_artifact_root = None;
            }
        }

        // STREAM the state into its receipt. Materializing it here put the whole
        // publication state in memory a seventh time, on top of the six
        // `complete_authorized_rows` calls — measured on ay: 17 -> 58 GB in
        // ninety seconds, then SIGKILL, after the verification had succeeded.
        let Some(session) = self
            .live_transport_authority
            .as_ref()
            .map(|authority| authority.verification_session.clone())
        else {
            return Err(SealRefusal::MissingLiveTransportAuthority);
        };
        let Ok(receipt) = streamed_complete_report_receipt(
            &self.report_subject,
            &session,
            self,
            self.proof_artifact_root.as_deref(),
            u64::try_from(crate::input_limits::max_emitted_proof_report_bytes())
                .unwrap_or(u64::MAX),
        ) else {
            return Err(SealRefusal::PublicationStateUnserializable);
        };
        let Some(authority) = self.live_transport_authority.as_mut() else {
            return Err(SealRefusal::MissingLiveTransportAuthority);
        };
        if !authority.seal_complete_report(
            &self.report_subject,
            &self.results,
            &self.zero_obligation_functions,
            &self.test_harness_exclusions,
            receipt,
            self.proof_artifact_root.as_deref(),
        ) {
            return Err(SealRefusal::CompleteReportReceiptRejected);
        }

        // Bind the exact canonical projection too. This rejects any internal
        // PASS whose rows cannot be attached one-for-one to the report that
        // users actually see, before terminal/JSON/HTML output begins.
        // ONE authorization for both steps below. Each mint is two whole-
        // publication-state serializations plus a pass over every row receipt,
        // and both steps run under the same `&self` borrow with no mutation
        // between them, so the second mint re-derived a value that could not
        // have changed. This is NOT a memo on the report: the token dies with
        // this borrow, and every later entry point still re-mints its own --
        // including the revocation below, which exists precisely so a failed
        // projection cannot be published.
        let (canonical, divergence) = {
            let authorized = self.complete_authorized_rows();
            let canonical = self.to_trust_report_with(authorized.as_ref());
            let divergence =
                self.canonical_report_state_divergence_with(&canonical, authorized.as_ref());
            (canonical, divergence)
        };
        if let Some(divergence) = divergence {
            if let Some(authority) = self.live_transport_authority.as_mut() {
                authority.complete_report_receipt = None;
                authority.canonical_report_receipt = None;
                authority.sealed_canonical_report = None;
                authority.sealed_canonical_bytes = None;
            }
            return Err(SealRefusal::CanonicalProjectionDiverged(divergence));
        }
        let Ok(serialized_canonical) = serialize_canonical_report_bounded(&canonical) else {
            return Err(SealRefusal::CanonicalReportUnserializable);
        };
        if self.live_transport_authority.as_mut().is_some_and(|authority| {
            authority.seal_canonical_report(&self.report_subject, canonical, serialized_canonical)
        }) {
            Ok(())
        } else {
            Err(SealRefusal::CanonicalReceiptRejected)
        }
    }

    /// Publish an HONEST fail-closed verdict when the final seal refused.
    ///
    /// A refused seal used to end the run at exit 2 with nothing printed —
    /// no `Summary:`, no `Gate:`, no coverage row. That is strictly worse than
    /// a failing verdict: a consumer reading only the exit status cannot tell a
    /// run that proved nothing from a run that REFUTED something, and
    /// `scripts/trust_endian_strict_gate.sh:370` does exactly that today.
    ///
    /// The repair is monotone DOWNWARD and cannot launder anything: every
    /// favorable row is graded `Unknown` with the refusal named verbatim, the
    /// outcome partition and gate are recomputed from the demoted vector, the
    /// gate is forced fail-closed, and authority is re-minted only through
    /// `recapture_over_unproved_rows`, which refuses outright if any row still
    /// claims proof. Nothing is published as proved that was not sealed —
    /// nothing is published as proved AT ALL.
    pub(crate) fn grade_every_row_unproved_and_reseal(
        &mut self,
        refusal: &SealRefusal,
        gate_exit_code: u8,
    ) -> Result<(), SealRefusal> {
        let reason = format!(
            "publication seal refused ({}); this obligation is graded unknown and carries no proof credit",
            refusal.precondition()
        );
        for result in &mut self.results {
            if matches!(
                result.outcome,
                VerificationOutcome::Proved | VerificationOutcome::RuntimeChecked
            ) {
                result.outcome = VerificationOutcome::Unknown;
                result.reason = Some(reason.clone());
            }
        }

        let (counts, _defects) = crate::pipeline::hardened::partition_outcome_counts(&self.results);
        self.proved = counts.proved;
        self.failed = counts.failed;
        self.unknown = counts.unknown;
        self.runtime_checked = counts.runtime_checked;
        self.assumed = counts.assumed;
        self.mandated = counts.mandated;
        self.contract_panics = counts.contract_panics;
        self.total = counts.total;
        self.success = false;

        // The gate keeps its lane, level, coverage and test-execution inventory
        // — those were established and are exactly what the caller must still
        // see — but its decision, counts and exit state become fail-closed.
        if let Some(gate) = self.gate.as_mut() {
            gate.decision = "inconclusive".to_string();
            gate.exit_code = gate_exit_code;
            gate.counts = trust_types::VerificationGateCounts {
                total: counts.total,
                proved: counts.proved,
                failed: counts.failed,
                unknown: counts.unknown,
                runtime_checked: counts.runtime_checked,
                assumed: counts.assumed,
                mandated: counts.mandated,
                contract_panics: counts.contract_panics,
                // Trust (CB4): exclusions are inventory, not rows this regrade
                // touches; the demotion leaves their count exactly as it was.
                excluded: gate.counts.excluded,
            };
            gate.conditional_on_assumption_rows = counts.assumed > 0;
            gate.conditional_on_runtime_checks = counts.runtime_checked > 0;
            // Same rule as the saved-report sanitizer in trust-types: this is a
            // DEMOTION to `inconclusive`, and the unknown-row condition is a
            // claim about a live conditional pass. It falls with the decision,
            // or the demoted gate contradicts itself and the diff lane's
            // cross-check refuses it.
            gate.conditional_on_unknown_rows = false;
        }
        // The rows changed, so their determinism accounting is recomputed
        // before the re-seal covers the gate.
        self.record_determinism();

        let subject = self.report_subject.clone();
        let zero_obligation_functions = self.zero_obligation_functions.clone();
        let test_harness_exclusions = self.test_harness_exclusions.clone();
        let recaptured = self.live_transport_authority.as_ref().and_then(|authority| {
            authority.recapture_over_unproved_rows(
                &subject,
                &self.results,
                zero_obligation_functions,
                test_harness_exclusions,
            )
        });
        let Some(recaptured) = recaptured else {
            return Err(refusal.clone());
        };
        self.live_transport_authority = Some(recaptured);
        self.seal_publication_state()
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
        Ok(LiveCanonicalReport { report, obligations: None })
    }

    /// Which internal-state invariant the canonical projection failed, if any.
    ///
    /// Returns the exact divergence rather than a bare bool: it is the only
    /// evidence the run has about WHY publication was refused, and it is
    /// printed with the refusal.
    #[cfg(test)]
    fn canonical_report_state_divergence(
        &self,
        report: &trust_types::JsonProofReport,
    ) -> Option<String> {
        self.canonical_report_state_divergence_with(
            report,
            self.complete_authorized_rows().as_ref(),
        )
    }

    /// `canonical_report_state_divergence` over an authorization the caller
    /// already holds. See [`Self::to_trust_report_with`] for why re-minting it under
    /// the same `&self` borrow cannot decide anything different.
    fn canonical_report_state_divergence_with(
        &self,
        report: &trust_types::JsonProofReport,
        live_authority: Option<&AuthorizedRows<'_>>,
    ) -> Option<String> {
        let Some(expected_unknown) = self
            .unknown
            .checked_add(self.assumed)
            .and_then(|value| value.checked_add(self.contract_panics))
        else {
            return Some(
                "internal unknown/assumed/contract-panic partition overflowed".to_string(),
            );
        };
        // The canonical projection recognizes a design mandate ONLY on an
        // AUTHORIZED row (`authorizes_row && counts_as_design_mandate`, see
        // `to_trust_report`): without live row authority the transport bit is
        // untrusted and the row conservatively classifies as unknown. Apply the
        // IDENTICAL gate to the expected counts, or a fail-closed run (e.g. a
        // strict compile abort, which has no complete authorized report) with a
        // mandate row would always mismatch here — turning the honest
        // developer-failure exit into a seal failure (exit 2).
        let authorized_mandated = {
            let authority = live_authority;
            self.results
                .iter()
                .enumerate()
                .filter(|(index, result)| {
                    authority
                        .as_ref()
                        .is_some_and(|authority| authority.authorizes_row(*index, result))
                        // NOT `transport_design_mandate` alone: the gate counts a
                        // mandate only on an INCONCLUSIVE row that survived the
                        // assumption/coroutine/contract-panic/unsupported branches.
                        // Reading the raw bit here counted rows the partition never
                        // did, and the difference underflowed `checked_sub` below.
                        && crate::pipeline::hardened::counts_as_design_mandate(result)
                })
                .count()
        };
        let Some(unauthorized_mandated) = self.mandated.checked_sub(authorized_mandated) else {
            // The authorized subset can never outnumber the raw partition.
            // Treat any internal accounting drift as a seal failure instead of
            // hiding it behind saturating arithmetic.
            return Some(format!(
                "authorized design-mandate rows ({authorized_mandated}) outnumber the internal mandate partition ({})",
                self.mandated
            ));
        };
        let Some(expected_unknown) = expected_unknown.checked_add(unauthorized_mandated) else {
            return Some("expected unknown partition overflowed".to_string());
        };
        let expected_mandated = authorized_mandated;
        let summary = &report.summary;
        let mut divergences = Vec::new();
        if report.verification_gate != self.gate {
            divergences.push("verification gate object".to_string());
        }
        if report.cargo_proof_inventory != self.cargo_proof_inventory {
            divergences.push("cargo proof inventory".to_string());
        }
        for (label, canonical_value, internal_value) in [
            ("total obligations", summary.total_obligations, self.total),
            ("proved", summary.total_proved, self.proved),
            ("failed", summary.total_failed, self.failed),
            ("runtime-checked", summary.total_runtime_checked, self.runtime_checked),
            ("design requirements", summary.total_design_requirements, expected_mandated),
            ("unknown", summary.total_unknown, expected_unknown),
            ("unattributed failed", summary.total_unattributed_failed, 0),
            ("unattributed unknown", summary.total_unattributed_unknown, 0),
            ("unattributed proved", summary.total_unattributed_proved, 0),
        ] {
            if canonical_value != internal_value {
                divergences.push(format!(
                    "{label} (canonical {canonical_value} vs internal {internal_value})"
                ));
            }
        }
        if !divergences.is_empty() {
            return Some(format!(
                "canonical projection disagrees with the internal outcome partition: {}",
                divergences.join(", ")
            ));
        }

        let Some(gate) = report.verification_gate.as_ref() else {
            return Some("canonical report carries no verification gate".to_string());
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
            return Some(
                "an unresolved Cargo Unit exclusion coexists with a success/pass verdict"
                    .to_string(),
            );
        }
        if gate_success != self.success {
            return Some(format!(
                "gate success ({gate_success}) disagrees with the run's success flag ({})",
                self.success
            ));
        }
        None
    }

    fn complete_authorized_rows(&self) -> Option<AuthorizedRows<'_>> {
        // STREAM the state into the receipt instead of materializing it. This
        // is called six times, and each materialization was the whole
        // publication state again — the 17 -> 58 GB climb that SIGKILLed ay's
        // release after its verification had already succeeded.
        let authority = self.live_transport_authority.as_ref()?;
        let receipt = streamed_complete_report_receipt(
            &self.report_subject,
            &authority.verification_session,
            self,
            self.proof_artifact_root.as_deref(),
            u64::try_from(crate::input_limits::max_emitted_proof_report_bytes())
                .unwrap_or(u64::MAX),
        )
        .ok()?;
        authority.validate_complete_report(
            &self.report_subject,
            &self.results,
            &self.zero_obligation_functions,
            &self.test_harness_exclusions,
            receipt,
            self.proof_artifact_root.as_deref(),
        )
    }

    /// Render the sealed verdict, and with `report_dir` also write the saved
    /// bundle. Returns that bundle's evidence status (`None` without
    /// `report_dir`); an INCOMPLETE bundle is not an error here — the verdict
    /// is still published — and the caller decides what it costs the exit code
    /// (see `pipeline::run::evidence_bundle_exit_override`).
    #[cfg(test)]
    pub(crate) fn render(
        &self,
        format: OutputFormat,
        report_dir: Option<&str>,
    ) -> io::Result<Option<EvidenceBundleStatus>> {
        self.render_with_unsafe_memory_report(format, report_dir, None)
    }

    /// `render` with an optional `--unsafe-memory` wrapper request. A wrapper
    /// request always demands a complete evidence bundle; the gate lane's own
    /// demand is passed by the CLI through [`Self::render_published`].
    #[cfg(test)]
    pub(crate) fn render_with_unsafe_memory_report(
        &self,
        format: OutputFormat,
        report_dir: Option<&str>,
        unsafe_memory: Option<&UnsafeMemoryReportRequest>,
    ) -> io::Result<Option<EvidenceBundleStatus>> {
        self.render_published(
            format,
            report_dir,
            unsafe_memory,
            unsafe_memory.is_some(),
            &mut io::stdout(),
        )
    }

    /// The one rendering path. `evidence_bundle_required` says whether this
    /// run ASKED for evidence (every lane but the advisory ramp, and any
    /// `--unsafe-memory` request — `pipeline::run::evidence_bundle_required`).
    /// When it did and the saved bundle came out INCOMPLETE, a machine format's
    /// stdout is WITHHELD: those runs exit 2, and the sealed bytes carry the
    /// gate's own `exit_code`/`decision`, which a stdout-only consumer would
    /// read as success. The verdict is then printed on stderr and the sealed
    /// report is still saved under `report_dir`.
    #[cfg(test)]
    pub(crate) fn render_published(
        &self,
        format: OutputFormat,
        report_dir: Option<&str>,
        unsafe_memory: Option<&UnsafeMemoryReportRequest>,
        evidence_bundle_required: bool,
        stdout: &mut dyn Write,
    ) -> io::Result<Option<EvidenceBundleStatus>> {
        self.render_published_with_compiler_resources(
            format,
            report_dir,
            unsafe_memory,
            evidence_bundle_required,
            CompilerResourceReports::default(),
            None,
            stdout,
        )
    }

    /// Preserve compiler lifecycle observations beside the sealed report.
    /// These observations are outside the proof DTO and its authority: the
    /// sidecar names the canonical bytes but cannot change their verdict.
    pub(crate) fn render_published_with_compiler_resources(
        &self,
        format: OutputFormat,
        report_dir: Option<&str>,
        unsafe_memory: Option<&UnsafeMemoryReportRequest>,
        evidence_bundle_required: bool,
        resources: CompilerResourceReports<'_>,
        delta: Option<&crate::agent_delta::DeltaView>,
        stdout: &mut dyn Write,
    ) -> io::Result<Option<EvidenceBundleStatus>> {
        // Once the output root is validated, clear an earlier wrapper before later refusals.
        if let Some(request) = unsafe_memory {
            let dir = report_dir.ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "unsafe-memory proof wrapper emission requires a report directory",
                )
            })?;
            invalidate_previous_unsafe_memory_wrapper(request, Path::new(dir))?;
        }
        // Minted once for this `&self` borrow and handed to the unsafe-memory
        // preflight below, which recomputed the identical token. `self` cannot
        // change while this borrow lives.
        let Some(authorized_rows) = self.complete_authorized_rows() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "canonical Targo output requires a valid final publication seal over rows, coverage, policy, gate, and exit state",
            ));
        };
        let unsafe_memory_preflight = if let Some(request) = unsafe_memory {
            Some(preflight_unsafe_memory_report(request, self, &authorized_rows)?)
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
        // BORROW, not clone. Every use below is `&trust_report`, and the seal
        // holds the DTO alive for the whole of `render`, so the clone bought
        // nothing and cost the largest single step in the report phase.
        // MEASURED 2026-09-19 on a 64 MiB window of a real 549 MB transport
        // corpus: +225.1 MiB of the run's 1010.0 MiB peak, more than any other
        // stage, for a report whose serialized form is 71.5 MiB. It is a
        // whole-graph deep copy, so it scales with the report, not with the run.
        let trust_report = sealed_report;
        if report_contains_ambient_path_materializations(trust_report) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "sealed canonical report retained proof evidence behind an AMBIENT path — \
                 a content-addressed `<store>/sha256/<digest>` path is permitted because the \
                 seal binds that digest, but any other path names something the capability \
                 does not bind",
            ));
        }
        let html_report = (matches!(format, OutputFormat::Html) || report_dir.is_some())
            .then(|| trust_report::html_report::generate_html_report(trust_report));

        // Persist requested evidence before printing machine-readable stdout so
        // consumers cannot observe a success-shaped report from a failed
        // artifact gate. A real I/O or integrity failure is still fatal here,
        // before any stdout. Crossing the store's COPY cap is not: the bundle
        // is committed with the overflow omitted and recorded in its
        // `evidence-bundle.json`, the unsafe-memory wrapper is withheld, and
        // the verdict is still published below (blocker 4, 2026-10-01: the cap
        // used to discard a verdict that had already sealed). Where the run
        // demanded a complete bundle it will exit 2, so a machine format's
        // stdout is withheld rather than letting the sealed, success-shaped
        // bytes stand beside that failure.
        let evidence_bundle = if let Some(dir) = report_dir {
            let output_dir = Path::new(dir);
            match write_report_artifacts_from_root_with_compiler_resources(
                trust_report,
                output_dir,
                html_report
                    .as_deref()
                    .expect("HTML report should be rendered when writing report artifacts"),
                self.proof_artifact_root.as_deref(),
                unsafe_memory_preflight,
                Some(serialized_canonical),
                resources,
            ) {
                Ok(status) => Some(status),
                Err(error) => {
                    // A real I/O or integrity failure (the copy cap no longer
                    // lands here: it omits and is disclosed instead). A run that
                    // finished verifying must not end with NOTHING to read
                    // (verified-lane blockers issue, item 4; 80d00f02b0,
                    // c3b6bab868). In EVERY format the counts go to STDERR as
                    // human text with the run's `Result:` replaced; stdout stays
                    // empty (in JSON mode it only ever carries the sealed
                    // canonical bytes, and none are printed for an unsaved
                    // report), so nothing success-shaped reaches a consumer, and
                    // the exit stays the gate failure's.
                    for line in self.unpublished_terminal_lines(&error) {
                        eprintln!("{line}");
                    }
                    return Err(error);
                }
            }
        } else {
            None
        };

        // Alias normalization must not hide why the compiler refused the run.
        // Keep this diagnostic-only disclosure on stderr in machine-readable
        // modes; stdout remains the exact sealed canonical report.
        if !matches!(format, OutputFormat::Terminal) {
            for line in self.elided_publication_diagnostic_lines() {
                eprintln!("{line}");
            }
        }

        let evidence_gate_fails = evidence_bundle_required
            && evidence_bundle.as_ref().is_some_and(|status| !status.complete);
        match format {
            OutputFormat::Terminal if evidence_gate_fails => {
                // This run exits 2 on the evidence gate: its counts are shown,
                // but no `Result:` or bare `Gate:` pass stands beside that exit
                // (the guarantee 80d00f02b0 made for an unsaved report).
                for line in self.evidence_gate_failed_terminal_lines() {
                    eprintln!("{line}");
                }
                eprintln!();
                eprintln!(
                    "{}",
                    summary_with_overridden_gate(&trust_report::format_json_summary(trust_report))
                );
            }
            OutputFormat::Terminal => {
                for line in self.terminal_lines_with(delta) {
                    eprintln!("{line}");
                }
                // Also print the trust-report text summary for richer output.
                eprintln!();
                eprintln!("{}", trust_report::format_json_summary(trust_report));
            }
            OutputFormat::Json | OutputFormat::Html if evidence_gate_fails => {
                // The verdict is still published: on the human stream, and in
                // the saved report.json named by the lines below, with the
                // `Result:` and `Gate:` lines framed by the evidence-gate exit.
                for line in self.evidence_gate_failed_terminal_lines() {
                    eprintln!("{line}");
                }
                eprintln!();
                eprintln!(
                    "{}",
                    summary_with_overridden_gate(&trust_report::format_json_summary(trust_report))
                );
                eprintln!(
                    "targo trust: {} stdout WITHHELD: this run requires a complete evidence bundle and will exit 2, and the sealed report's own gate fields must not read as success beside that exit; the sealed report is saved at {}",
                    if matches!(format, OutputFormat::Json) { "JSON" } else { "HTML" },
                    report_dir
                        .map(|dir| report_artifact_path(Path::new(dir), ReportArtifact::Json))
                        .unwrap_or_default()
                        .display()
                );
            }
            OutputFormat::Json => {
                // Emit the exact compact bytes covered by the canonical seal.
                stdout.write_all(serialized_canonical)?;
                stdout.write_all(b"\n")?;
                stdout.flush()?;
            }
            OutputFormat::Html => {
                // Use trust-report HTML generator with dashboard.
                writeln!(
                    stdout,
                    "{}",
                    html_report
                        .as_deref()
                        .expect("HTML output should be rendered when format=html")
                )?;
                stdout.flush()?;
            }
        }

        // The changed-only view (`crate::agent_delta`) on the human stream of
        // every rendering that did not place it among the terminal rows.
        if let Some(delta) = delta {
            if evidence_gate_fails || !matches!(format, OutputFormat::Terminal) {
                for line in delta.lines() {
                    eprintln!("{line}");
                }
            }
        }

        // Next to the verdict, on the human stream in every format (stdout of
        // a machine format stays the exact sealed bytes).
        if let (Some(status), Some(dir)) = (evidence_bundle.as_ref(), report_dir) {
            for line in evidence_bundle_incomplete_lines(status, Path::new(dir)) {
                eprintln!("{line}");
            }
        }

        Ok(evidence_bundle)
    }

    /// The terminal report for a run whose report artifacts could not be
    /// written: the per-row and `Summary:` lines as measured, framed as NOT
    /// PUBLISHED, and the `Result:` line replaced so no pass is ever printed for
    /// a run that exits on the artifact gate.
    fn unpublished_terminal_lines(&self, error: &io::Error) -> Vec<String> {
        let mut lines = vec![
            String::new(),
            format!("=== REPORT NOT SAVED: {error} ==="),
            "The counts below are what this run measured. No report was written, so \
             they are not a published or sealed verdict."
                .to_string(),
        ];
        lines
            .extend(self.terminal_lines().into_iter().filter(|line| !line.starts_with("Result: ")));
        lines
            .push(format!("Result: NOT PUBLISHED (report artifact evidence gate failed: {error})"));
        lines
    }

    /// The terminal report for a run that saved its report but exits 2 because
    /// it requires a complete evidence bundle and the bundle came out
    /// incomplete: every measured line, with the run's own `Result:` replaced
    /// in place, so no pass is printed for a run that fails the evidence gate.
    fn evidence_gate_failed_terminal_lines(&self) -> Vec<String> {
        self.terminal_lines()
            .into_iter()
            .map(|line| {
                if line.starts_with("Result: ") {
                    EVIDENCE_GATE_FAILED_RESULT.to_string()
                } else {
                    line
                }
            })
            .collect()
    }

    fn terminal_lines(&self) -> Vec<String> {
        self.terminal_lines_with(None)
    }

    /// The terminal report. With a changed-only view
    /// (`crate::agent_delta::DeltaView`) the per-row listing is narrowed, when
    /// `DeltaView::replaces_listing` says so, to the listing's own line of
    /// every row it does not label a plain `PROVED` — whatever package the
    /// row belongs to, keyed or not, with its message, location and backend —
    /// followed by the view's lines; otherwise the view follows the whole
    /// listing. So the view never prints less about a row that is not plainly
    /// proved than the listing does. Every other line, the `Summary:` and gate
    /// lines and an empty run's `No verification obligations found.` included,
    /// is the same either way.
    fn terminal_lines_with(&self, delta: Option<&crate::agent_delta::DeltaView>) -> Vec<String> {
        let mut lines = Vec::with_capacity(self.results.len() + 8);
        lines.push(String::new());
        lines.push("=== Trust Verification Report ===".to_string());
        let profile = &self.config.budget_profile;
        lines.push(format!("Level: {} | Duration: {}ms", self.config.level, self.duration_ms));
        // Determinism plan §3.6: the profile id and its bounds, so two runs'
        // counts are comparable exactly when its id agrees, then the derived
        // clocks and the worker-thread count, which are not in the id.
        lines.push(profile.header_line());
        if let Some(requirements) = &self.config.project_requirements {
            lines.push(format!(
                "Project requirements: {} (Cargo project configuration; adopted for this run)",
                requirements.items().join(", ")
            ));
        }
        lines.push(String::new());

        match delta {
            Some(delta) if delta.replaces_listing() => {
                // The empty-listing line is no plainly proved row: an empty
                // run says so with a base as without one.
                if self.results.is_empty() {
                    lines.push("  No verification obligations found.".to_string());
                }
                // Not from the records: a row with no stable key, a row of a
                // package the run did not select and a second row under one
                // key are in no view row, and the listing's line carries the
                // row's message and location, which a record does not.
                lines.extend(
                    self.results
                        .iter()
                        .map(terminal_result_line_and_label)
                        .filter(|(_, label)| !listing_label_is_plain_proof(label))
                        .map(|(line, _)| line),
                );
                lines.extend(delta.lines());
            }
            _ => {
                if self.results.is_empty() {
                    lines.push("  No verification obligations found.".to_string());
                } else {
                    lines.extend(self.results.iter().map(terminal_result_line));
                }
                if let Some(delta) = delta {
                    lines.extend(delta.lines());
                }
            }
        }

        let full_verifier_lines =
            full_verifier_terminal_lines(&self.results, &self.compiler_diagnostics);
        if !full_verifier_lines.is_empty() {
            lines.push(String::new());
            lines.extend(full_verifier_lines);
        }

        lines.push(String::new());
        let determinism = self.determinism();
        if let Some(line) = determinism.could_not_run_line() {
            // Plan §2: a run the verifier was refused the resources for, or
            // whose rows carry no stable key (T9), has no count. No `Summary:`
            // line, so no consumer can read one as a floor measurement; the
            // phrase "verification did not run" is the one consumers already
            // treat as NOT-VERIFIED.
            lines.push(line);
        } else {
            lines.push(format!(
                "Summary: {} proved, {} failed, {} runtime-checked, {} assumed, {} mandated, {} contract-panic, {} inconclusive ({} total){}",
                self.proved,
                self.failed,
                self.runtime_checked,
                self.assumed,
                self.mandated,
                self.contract_panics,
                self.unknown,
                self.total,
                determinism.summary_suffix(&self.config.budget_profile),
            ));
        }
        // The `Summary:` line above is byte-stable (scripts grep it); the split
        // of its `failed` count rides its own line, present only when some
        // failed row was not refuted.
        if let Some(line) = failed_unproved_terminal_line(&self.results, self.failed) {
            lines.push(line);
        }
        // Distinct-site view of the failed rows, printed only when it differs
        // from the row count (a refuted MIR assert under the hardened profile
        // is two failed rows at one site). Informational: the Summary's
        // `failed` above is the row count the gate decides on.
        if determinism.outcome != trust_types::determinism::UnitOutcome::CouldNotRun {
            let failure_sites = self.failure_sites();
            if failure_sites.differs_from_row_count() {
                lines.extend(failure_sites.terminal_line());
            }
        }
        lines.push(determinism.stop_cause_line());
        // Trust (#220 — publication boundary): the compiler's favorable verdict
        // vector and the vector this report publishes are NOT the same set, and
        // until now the terminal said nothing about the difference.
        lines.push(self.publication_boundary_line());
        lines.extend(self.elided_publication_diagnostic_lines());
        // Trust (`--test-target-panics=runtime-checked`): empty unless the flag
        // actually reclassified something, so an absent flag adds no output.
        lines.extend(crate::test_target_panics::terminal_lines(&self.results));
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
        if let Some(line) = self.test_harness_exclusion_line() {
            lines.push(line);
        }
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

    /// Trust (#220): the human report's publication-boundary line.
    ///
    /// Every other view of this boundary under-reports it. `terminal_result_line`
    /// renders label/kind/message/location/solver/time and never `reason`, so a
    /// demoted row is indistinguishable from a solver `unknown`; the `Summary:`
    /// line has no bucket for one. And a reader who greps `--json` for the
    /// demotion reason sees only the rows that SURVIVED — demotion runs before
    /// `elide_rows_proved_only_by`, which deletes a demoted hardened-panic twin
    /// whose sibling published, leaving no proof row at all. So the counts and
    /// diagnostic identities come from the normalization pass itself.
    ///
    /// Disclosure only: no verdict, no row, and no demotion criterion moves.
    fn publication_boundary_line(&self) -> String {
        let Some(boundary) = self.publication_boundary.as_ref() else {
            return "Publication boundary: not measured (this report was not built from an \
                    authenticated compiler vector)"
                .to_string();
        };
        let withheld = boundary.withheld();
        if withheld == 0 {
            return format!(
                "Publication boundary: {} obligation(s) passed the compiler, all {} published \
                 (0 withheld)",
                boundary.compiler_favorable, boundary.published_favorable,
            );
        }
        let relabelled_unknown = boundary
            .withheld_relabelled
            .saturating_sub(boundary.withheld_relabelled_runtime_checked);
        let mut split = vec![format!(
            "{relabelled_unknown} relabelled unknown (visible in --json with the reason)"
        )];
        if boundary.withheld_relabelled_runtime_checked > 0 {
            split.push(format!(
                "{} relabelled runtime-checked under policy B (a compiler proof claim without \
                 attachable evidence, on a kind whose runtime check rustc always emits; counted \
                 conditional, never proved; visible in --json with the reason)",
                boundary.withheld_relabelled_runtime_checked
            ));
        }
        split.push(format!(
            "{} deleted as a redundant alias (identity disclosed separately; no proof credit)",
            boundary.withheld_elided
        ));
        let unattributed = boundary.unattributed_withheld();
        if unattributed > 0 {
            split.push(format!("{unattributed} unattributed — publication accounting defect"));
        }
        format!(
            "Publication boundary: {} obligation(s) passed the compiler, {} published, \
             {} WITHHELD for want of clean-kernel or publishable native proof evidence \
             ({}). See docs/TCB.md \"The publication boundary\".",
            boundary.compiler_favorable,
            boundary.published_favorable,
            withheld,
            split.join("; "),
        )
    }

    /// Retain exact request identities for rows omitted by publication
    /// normalization. In particular, an Unknown hardened twin can still be the
    /// reason for a nonzero compiler exit even when all visible rows are proved.
    /// These records never modify the row denominator, verdict, or proof seal.
    fn elided_publication_diagnostic_lines(&self) -> Vec<String> {
        let Some(boundary) = self.publication_boundary.as_ref() else {
            return Vec::new();
        };
        if boundary.elided_diagnostics.is_empty() {
            return Vec::new();
        }
        let mut lines = vec![format!(
            "Compiler requests omitted from the published proof rows: {} (diagnostics only; not discharged by this report)",
            boundary.elided_diagnostics.len(),
        )];
        for diagnostic in &boundary.elided_diagnostics {
            lines.push(format!(
                "  [{}{}] function={} obligation={} kind={} claim_sha256={}",
                diagnostic.outcome.label(),
                if diagnostic.withheld { "; proof withheld at publication" } else { "" },
                diagnostic.function,
                diagnostic.obligation_id.as_deref().unwrap_or("unavailable"),
                diagnostic.kind,
                diagnostic.claim_digest_sha256.as_deref().unwrap_or("unavailable"),
            ));
            lines.push(format!(
                "    goal description: {} @ {}",
                diagnostic.message,
                diagnostic.source_location.as_deref().unwrap_or("location unavailable"),
            ));
            lines.push(format!(
                "    backend={} suite={} request_id={} native_id={}",
                diagnostic.backend,
                diagnostic.native_suite.as_deref().unwrap_or("unavailable"),
                diagnostic.native_request_id.as_deref().unwrap_or("unavailable"),
                diagnostic.native_id.as_deref().unwrap_or("unavailable"),
            ));
            if let Some(reason) = &diagnostic.reason {
                lines.push(format!("    compiler/publication reason: {reason}"));
            }
        }
        lines.push(
            "  Next: resolve or replay evidence for the exact request above under the original compiler policy, then rerun the check. An alias or a proved sibling is not replay authority; the compiler refusal and final gate remain unchanged."
                .to_string(),
        );
        lines
    }

    /// Trust (CB4): ONE line per run naming the excluded libtest harness bodies
    /// by count — never one line per body, which would grow with the number of
    /// tests. The per-body inventory is in `report.json`
    /// (`verification_gate.exclusions`). `None` outside a test-harness build.
    fn test_harness_exclusion_line(&self) -> Option<String> {
        let exclusions = &self.test_harness_exclusions;
        if exclusions.is_empty() {
            return None;
        }
        let closures = exclusions
            .iter()
            .filter(|exclusion| {
                exclusion.item
                    == trust_types::exclusion::TestHarnessExclusionItem::TestRunnerClosure.tag()
            })
            .count();
        let mains = exclusions.len() - closures;
        Some(format!(
            "Excluded [{}]: {} body/bodies rustc's libtest harness synthesized ({} test runner \
             closure(s), {} harness main(s)) — NOT verified and NOT proved; they carry no user \
             code, and every test function they call is verified as its own body",
            trust_types::exclusion::TEST_HARNESS_EXCLUSION_TAG,
            exclusions.len(),
            closures,
            mains,
        ))
    }

    /// Trust (assertion-grade coverage): the human report's coverage line.
    fn coverage_line(&self) -> String {
        match &self.coverage {
            // Trust (CB4): in a test-harness build some processed bodies were
            // EXCLUDED (rustc's libtest harness code), not verified. Say so,
            // with the split, instead of calling every processed body verified.
            Some(cov) if cov.coverage_complete && cov.excluded > 0 => format!(
                "Coverage: {}/{} eligible function bodies accounted for ({} verified, {} excluded: {}) (complete)",
                cov.processed,
                cov.eligible,
                cov.processed.saturating_sub(cov.excluded),
                cov.excluded,
                trust_types::exclusion::TEST_HARNESS_EXCLUSION_TAG,
            ),
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
            None if !self.coverage_dropped.is_empty() => {
                let more = self.coverage_dropped.len() - 1;
                format!(
                    "Coverage: unknown (the compiler emitted a coverage_summary transport row and \
                     targo dropped it: {}{})",
                    self.coverage_dropped[0],
                    if more == 0 { String::new() } else { format!("; and {more} more") },
                )
            }
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
                // Ramp (2026-09-07): the advisory lane carries genuine unknowns
                // as conditions of the pass. They LEAD the list — a pass that
                // stands on unproved obligations must never read like one that
                // stands on ledger rows alone — and they are not in the
                // Assumptions ledger, so the pointer names the Gate line too.
                "conditional-pass" if gate.exit_code == 0 => format!(
                    "PASS (conditional: {} unproved, {} assumption{}, {} design mandate{}, {} runtime-checked, {} contract-panic{}; see the Gate line and the Assumptions ledger)",
                    gate.counts.unknown,
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
                // T7b: no measurement, nothing refuted — exit 3, never a pass
                // and never an unproved verdict.
                "could-not-run" => format!(
                    "COULD NOT RUN (outcome {}: not a measurement, so its counts are no \
                     verdict; see the Stop causes line; exit {})",
                    gate.determinism
                        .as_ref()
                        .map_or("could-not-run", |block| block.outcome.as_str()),
                    gate.exit_code,
                ),
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
    #[cfg(test)]
    fn to_trust_report(&self) -> trust_types::JsonProofReport {
        self.to_trust_report_with(self.complete_authorized_rows().as_ref())
    }

    /// `to_trust_report` over an authorization the caller already holds.
    ///
    /// Minting that authorization costs TWO whole-publication-state
    /// serializations (`streamed_complete_report_receipt` counts the state, then
    /// hashes it) plus one pass over every row receipt. A caller that already
    /// holds an `AuthorizedRows` holds it under a `&self` borrow, and `self`
    /// cannot change while that borrow lives, so re-minting here could not
    /// decide anything different -- it would only pay for the same answer again.
    fn to_trust_report_with(
        &self,
        live_authority: Option<&AuthorizedRows<'_>>,
    ) -> trust_types::JsonProofReport {
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
                // The SAME predicate the gate uses, for the same reason as
                // `authorized_mandated` in `canonical_report_state_divergence`:
                // reading the raw `design_mandate` bit here labels a row a design
                // REQUIREMENT that the gate counted in another bucket entirely. A
                // FAILED row carrying the bit is `failed` to the partition (the
                // outcome match runs before the mandate test, which only sees
                // Unknown/Timeout) but became a DesignRequirement canonically — so
                // it left `total_failed`. MEASURED on trust-wp 2026-09-13, once
                // the mandate-count fix exposed it: `total_failed 1113 != 1185`,
                // exactly 72 such rows.
                let compiler_design_mandate = live_authority.as_ref().is_some_and(|authority| {
                    authority.authorizes_row(index, r)
                        && crate::pipeline::hardened::counts_as_design_mandate(r)
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
                // The SAME resolver that decided this row is a mandate, so the
                // label cannot go missing on a row the gate counted.
                let mandate_category =
                    if compiler_design_mandate { hardened_mandate_category(r) } else { None };
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
                // Every row the GATE diverts as conditional evidence, not just the
                // declared contract panics this used to check: an `assumption:*`
                // ledger entry, a published coroutine resume-state contract, and a
                // row discharged under one. The gate counts them `assumed` /
                // `contract_panics` and the seal expects them among the canonical
                // unknowns, so a FAILED assumption row mapped to a canonical
                // FAILURE disagrees with the gate AND publishes conditional
                // evidence as a refutation.
                let declared_contract_panic = is_declared_contract_panic_result(r);
                let contract_panic = declared_contract_panic
                    || crate::pipeline::hardened::counts_as_conditional_evidence(r);
                let vr = if contract_panic {
                    TrustVr::Unknown {
                        solver: r.backend.clone().into(),
                        time_ms: r.time_ms.unwrap_or(0),
                        reason: conditional_evidence_report_reason(declared_contract_panic)
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
        // Trust (TINV step 10.7): every row keeps the compiler's `assumes` disclosure,
        // whatever outcome it ends with here (a row this lane withholds keeps it too).
        let unattached_assumes = attach_transport_assumes(&mut report, &self.results);
        if live_authority.is_some() {
            report.functions.extend(
                self.zero_obligation_functions.iter().cloned().map(zero_obligation_function_report),
            );
            report.functions.sort_by(|left, right| left.function.cmp(&right.function));
        }
        self.attach_live_transport_evidence(
            &mut report,
            &full_verifier_diagnostics,
            live_authority,
        );
        append_full_verifier_unknown_diagnostics(
            &mut report,
            &self.results,
            &full_verifier_diagnostics,
        );
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
            // Trust (`--test-target-panics=runtime-checked`): a reclassified
            // panic-class test-target row is a CONDITION of this run's verdict,
            // so it is listed here with the reason that names the flag and the
            // exact cargo target. The row is also still an obligation above
            // (RuntimeChecked, never Proved) and still counted by the gate; the
            // ledger is where a reader sees the complete set at a glance.
            .chain(self.results.iter().filter_map(crate::test_target_panics::ledger_entry))
            // Trust (TINV step 10.7): a row whose verdict rests on a certified type
            // invariant is listed once per premise, under its own tag.
            .chain(self.results.iter().flat_map(type_invariant_assumption_entries))
            // Review fold-in: a premise the report could not place on its row is a
            // named diagnostic, never silently dropped.
            .chain(unattached_assumes)
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
        // Resolve every target before changing any report row. This keeps the
        // result/evidence pairing atomic: a grouping/cardinality mismatch makes
        // the whole attachment step fail closed instead of partially promoting
        // an index-shifted prefix.
        //
        // That atomicity is a claim about TARGETS, not about payloads: every
        // early `return` below is a grouping/cardinality defect decided from the
        // row's function name and this function's obligation cursor, and the
        // evidence projection cannot fail. So this pass keeps only the resolved
        // slot pair and the second pass projects each row's evidence straight
        // into its slot. Collecting the evidence here instead held the whole
        // transport envelope of every row AND the proof-evidence report of
        // every authorized row live at once, in a 1048-byte-per-row tuple, for
        // the entire corpus before one of them was moved into the report.
        // MEASURED on the compiler transport corpus 2026-09-19 with a counting
        // global allocator bracketing this function: that staging was 12.0-21.7
        // MiB of transient heap over windows of 2,433-10,693 rows, 13-32% of
        // the stage's peak, and it scales with the row count.
        let mut targets = Vec::with_capacity(self.results.len());
        for result in &self.results {
            let function_name = report_function_name(result);
            let Some(function_index) = function_indices.get(&function_name).copied() else {
                return;
            };
            let obligation_index = cursors[function_index];
            if obligation_index >= report.functions[function_index].obligations.len() {
                return;
            }
            cursors[function_index] += 1;
            targets.push((function_index, obligation_index));
        }
        if cursors
            .iter()
            .enumerate()
            .any(|(index, cursor)| *cursor != report.functions[index].obligations.len())
        {
            return;
        }

        // Every target is resolved and every cardinality check above has
        // passed, so this pass cannot fail: it projects one row's evidence and
        // moves it into that row's slot before the next row is decoded, and one
        // row's evidence is live outside the report at a time.
        //
        // `native_transport_evidence` still CLONES out of the decoded record
        // rather than consuming it, and deliberately: the record comes from
        // `serde_json`, whose buffers carry growth slack, and a clone allocates
        // exactly the length it copies. MEASURED the same way, consuming the
        // record instead retained that slack in the report — +62.8 MB on a
        // 10,693-row window, which cost more than the staging above saved.
        for (result_index, result) in self.results.iter().enumerate() {
            let (function_index, obligation_index) = targets[result_index];
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
                    .or_else(|| {
                        source_clause::proof_evidence_report(
                            result,
                            structured.as_ref(),
                            self.proof_artifact_root.as_deref(),
                        )
                    })
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
            let time_ms = result.time_ms.unwrap_or(0);
            let obligation_id = structured.and_then(|evidence| evidence.obligation_id);

            let obligation = &mut report.functions[function_index].obligations[obligation_index];
            obligation.obligation_id = obligation_id;
            obligation.transport_evidence = transport_evidence;
            match (outcome, proof_evidence) {
                (VerificationOutcome::Proved, Some(proof)) => {
                    obligation.outcome =
                        ObligationOutcome::Proved { strength: proof.strength.clone() };
                    obligation.evidence = Some(proof.evidence.clone());
                    obligation.proof_evidence = Some(proof);
                    // The published `proof_evidence` above was projected from
                    // the SAME structured transport record that
                    // `native_transport_evidence` cloned into the envelope, so
                    // the envelope's copy is an exact duplicate on every field
                    // the saved-report decoder compares. Drop it — on these
                    // rows only, and only after that comparison agrees — so
                    // each proof artifact is written once. This edits the
                    // canonical PROJECTION; `self.results` (the raw rows every
                    // row receipt and the complete-report receipt hash) is
                    // `&self` here and is never touched.
                    trust_types::elide_duplicate_transport_proof_evidence(obligation);
                }
                (VerificationOutcome::RuntimeChecked, _) => {
                    obligation.outcome = ObligationOutcome::RuntimeChecked { note: reason };
                    obligation.evidence = None;
                    obligation.proof_evidence = None;
                }
                (VerificationOutcome::Timeout, _)
                    // Never clobber a DESIGN REQUIREMENT. `to_trust_report`
                    // classifies an authorized design mandate as one, and the
                    // gate counts a mandate on an `Unknown` OR `Timeout` row —
                    // so overwriting a TIMED-OUT mandate with `Timeout` here
                    // drops it out of `total_design_requirements` while the gate
                    // still counts it in `mandated`. MEASURED on trust-wp
                    // 2026-09-13: 261 mandated against 227 design requirements,
                    // exactly the 34 timed-out ones. A mandate is a statement
                    // about the obligation's STATUS, not about how long the
                    // solver spent before giving up on it.
                    if !matches!(obligation.outcome, ObligationOutcome::DesignRequirement { .. }) => {
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
            failed_unproved: 0,
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
        CertifiedTestExecutionCompletionScope::RetainedCompileCheckpointAndChildExitV1 => {
            "retained-compile-checkpoint-and-child-exit-v1"
        }
    };
    let phase_a_kind = match execution.completion_scope {
        CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1 => "phase_a_exit",
        CertifiedTestExecutionCompletionScope::RetainedCompileCheckpointAndChildExitV1 => {
            "phase_a_compile_checkpoint_status"
        }
    };
    let mut fields = vec![
        format!("schema={}", execution.schema),
        format!("completion_scope={completion_scope}"),
        format!("state={state}"),
        format!("requested={}", execution.requested),
        format!("compile_only={}", execution.compile_only),
        format!("{phase_a_kind}={}", execution.phase_a_status),
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
pub(crate) fn assumption_entry_from_result(
    result: &VerificationResult,
) -> Option<trust_types::AssumptionEntry> {
    // Trust (2026-09-16): the DISCHARGED global-alloc dealloc contract is
    // conditional evidence disclosed in the same ledger, under its own tag.
    let tag = if result.kind == trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND {
        "global-alloc-dealloc-vacuous"
    } else if trust_types::assumption::is_instance_hypothesis_discharge_row(
        &result.kind,
        &result.backend,
    ) {
        // Trust (OD-1 phase 1): a `proved` instance-discharge row is CONDITIONAL
        // evidence — the gate counts it `assumed` (`partition_outcome_counts`) — so
        // it is listed here too, or the gate's assumed count and this ledger
        // disagree. A failed or unknown discharge is an outcome, not a condition.
        if !result.outcome.is_proved() {
            return None;
        }
        trust_types::assumption::INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND
    } else {
        result.kind.strip_prefix("assumption:")?
    };
    Some(trust_types::AssumptionEntry {
        scope: "function".to_string(),
        subject: result.function.clone(),
        tag: tag.to_string(),
        detail: result.message.clone(),
        location: result.location.clone(),
        source: result.backend.clone(),
    })
}

pub(crate) fn report_vc_kind(result: &VerificationResult) -> VcKind {
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
    if result.kind == trust_types::assumption::INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND {
        // Trust (OD-1 phase 1): an instance-discharge row reports the resolved
        // callee's verdict for one (site, instance); it is no Rust runtime check, so
        // the `Assertion` fallback below would both drop its text (site, instance,
        // callee) and falsely claim a runtime fallback. `UnsupportedMir` is the
        // no-proof, no-fallback carrier and keeps the compiler's description.
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

/// Trust (TINV step 10.7): copy each transport row's `assumes` disclosure onto its report
/// row. Positional like [`restore_typed_transport_descriptions`] when the function grouping
/// is a one-to-one projection of `results`. Otherwise (review fold-in) the disclosure is
/// NOT silently dropped: each premise-carrying row is attached by its exact, UNIQUE
/// obligation id within its function, and every row that still cannot be placed is
/// returned as a ledger diagnostic (tag [`TYPE_INVARIANT_UNATTACHED_TAG`]) naming the
/// function and its premises. Disclosure only.
#[must_use]
fn attach_transport_assumes(
    report: &mut trust_types::JsonProofReport,
    results: &[VerificationResult],
) -> Vec<trust_types::AssumptionEntry> {
    let function_indices = report
        .functions
        .iter()
        .enumerate()
        .map(|(index, function)| (function.function.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut cursors = vec![0usize; report.functions.len()];
    let mut attachments = Vec::new();
    let mut aligned = true;
    for result in results {
        let Some(function_index) = function_indices.get(&report_function_name(result)).copied()
        else {
            aligned = false;
            break;
        };
        let obligation_index = cursors[function_index];
        if obligation_index >= report.functions[function_index].obligations.len() {
            aligned = false;
            break;
        }
        cursors[function_index] += 1;
        let assumes = transport_assumes(result);
        if !assumes.is_empty() {
            attachments.push((function_index, obligation_index, assumes));
        }
    }
    if aligned
        && cursors
            .iter()
            .enumerate()
            .all(|(index, cursor)| *cursor == report.functions[index].obligations.len())
    {
        for (function_index, obligation_index, assumes) in attachments {
            report.functions[function_index].obligations[obligation_index].assumes = assumes;
        }
        return Vec::new();
    }
    attach_transport_assumes_by_obligation_id(report, results)
}

/// The fallback of [`attach_transport_assumes`]: attach by exact obligation id (unique
/// within the row's function), and report every premise-carrying row that cannot be placed.
fn attach_transport_assumes_by_obligation_id(
    report: &mut trust_types::JsonProofReport,
    results: &[VerificationResult],
) -> Vec<trust_types::AssumptionEntry> {
    let mut unattached = Vec::new();
    for result in results {
        let assumes = transport_assumes(result);
        if assumes.is_empty() {
            continue;
        }
        let function = report_function_name(result);
        let id = crate::types::structured_transport_evidence(result)
            .and_then(|evidence| evidence.obligation_id);
        let mut hits = Vec::new();
        if let Some(id) = id.as_deref() {
            for (fi, f) in report.functions.iter().enumerate() {
                if f.function != function {
                    continue;
                }
                for (oi, o) in f.obligations.iter().enumerate() {
                    if o.obligation_id.as_deref() == Some(id) {
                        hits.push((fi, oi));
                    }
                }
            }
        }
        if let [(fi, oi)] = hits[..] {
            report.functions[fi].obligations[oi].assumes = assumes;
        } else {
            unattached.push(trust_types::AssumptionEntry {
                scope: "function".to_string(),
                subject: result.function.clone(),
                tag: TYPE_INVARIANT_UNATTACHED_TAG.to_string(),
                detail: format!(
                    "the report could not place this row's `assumes` disclosure on its \
                     obligation row (the function grouping is not a one-to-one projection of \
                     the transport rows and no unique obligation id matched; {} candidate(s)); \
                     the row's verdict rests on: {}",
                    hits.len(),
                    assumes.join("; ")
                ),
                location: result.location.clone(),
                source: "trust-tinv".to_string(),
            });
        }
    }
    unattached
}

/// Trust (TINV step 10.7, review fold-in): the ledger tag of a premise-carrying row whose
/// `assumes` could not be placed on its report row.
pub(crate) const TYPE_INVARIANT_UNATTACHED_TAG: &str = "type-invariant-unattached";

/// Trust (TINV step 10.7): the transport row's `assumes` disclosure lines, or none.
pub(crate) fn transport_assumes(result: &VerificationResult) -> Vec<String> {
    crate::types::structured_transport_evidence(result)
        .map(|evidence| evidence.assumes)
        .unwrap_or_default()
}

/// Trust (TINV step 10.7): the assumption-ledger entries of one row whose verdict rests
/// on a certified type invariant, one per premise, tag `type-invariant`.
pub(crate) fn type_invariant_assumption_entries(
    result: &VerificationResult,
) -> Vec<trust_types::AssumptionEntry> {
    transport_assumes(result)
        .into_iter()
        .map(|premise| trust_types::AssumptionEntry {
            scope: "function".to_string(),
            subject: result.function.clone(),
            tag: TYPE_INVARIANT_ASSUMPTION_TAG.to_string(),
            detail: premise,
            location: result.location.clone(),
            source: "trust-tinv".to_string(),
        })
        .collect()
}

/// Trust (TINV step 10.7): the assumption-ledger tag of a type-invariant premise.
pub(crate) const TYPE_INVARIANT_ASSUMPTION_TAG: &str = "type-invariant";

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
    hardened_mandate_category(result).is_some()
}

/// WHICH hardened category a design-mandate row mandates, or `None` if it is not
/// a design mandate at all.
///
/// This is the single resolution the predicate and the canonical label must
/// share. They did not: `transport_design_mandate` accepted a row through EITHER
/// the typed payload's `hardened_category()` or the `hardened_*` spelling of its
/// compact tag, while `to_trust_report` looked the category up with
/// `parse_hardened_category` — the tag path ALONE. A typed hardened VC whose
/// compact tag is not spelled `hardened_…` therefore counted as a mandate for the
/// gate and resolved to no category for the report, so it could not be labelled a
/// design requirement and silently became an ordinary unknown. MEASURED on
/// trust-wp 2026-09-13: `total_design_requirements 227 != authorized_mandated
/// 261` — 34 rows.
///
/// Resolving it in one place means the question "is this a mandate?" and the
/// question "which mandate is it?" cannot be answered differently.
pub(crate) fn hardened_mandate_category(result: &VerificationResult) -> Option<HardenedVcCategory> {
    if !crate::types::structured_transport_vc_kind_is_authority_safe(result)
        || !structured_transport_evidence(result).is_some_and(|evidence| evidence.design_mandate)
    {
        return None;
    }

    // The bit is meaningful only for hardened-category VCs.  Bind a modern
    // row to its exact typed category, and preserve fieldless compatibility
    // only for tags in the explicit hardened namespace. Otherwise a
    // self-consistent DivisionByZero/Postcondition row with a stray bit could
    // be removed from the proof denominator as though it were a design-only mandate.
    let category = match exact_transport_vc_kind(result) {
        // The typed category first, the tag as the fallback the predicate always
        // allowed — never a fabricated one: a row that names no category is not
        // a design mandate here, exactly as before.
        Ok(Some(kind)) => {
            kind.hardened_category().or_else(|| parse_hardened_category(&result.kind))
        }
        Ok(None) => parse_hardened_category(&result.kind),
        Err(()) => None,
    };
    // G3-MANDATE-L1-ONLY-1 (2026-10-27): a design mandate is an L1 profile
    // rule. An L0 `UnsafeOperation`/`FfiBoundary` row's tautological violation
    // is a modelling-gap fail-close (an FFI call with no summary, an
    // `[unsafe:unmodeled-call]`, the `[unsafe] missing SAFETY comment`
    // stand-in), and the compiler no longer sets the bit on one
    // (`VcKind::is_hardened_design_mandate`). A row that still carries it (an
    // older compiler, a hand-made report) is NOT a mandate here either: it stays
    // in its outcome bucket for the gate, and trust-report, which applies the
    // same predicate, does not label it a design requirement, so the gate and
    // the canonical projection keep agreeing.
    category.filter(|category| category.admits_design_mandate())
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
                // KR0 switch: the row names the Clean reference entry's
                // theory and environment, or it is not Certified. An evidence
                // record written before the switch has neither and is withheld.
                && evidence.is_certified()
        })
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
    if !clean_cic_replay_diagnostic_matches(result, proof, &decoded) {
        return false;
    }
    if term.is_empty()
        || context.is_empty()
        || lineage.algorithm != trust_ir::ProofDigestAlgorithm::Sha256
        || lineage.is_zero()
        || serde_json::to_value(&decoded).ok().as_ref() != Some(metadata)
    {
        return false;
    }
    // The content address is over the TYPED certificate's serde_json encoding
    // (fields in declaration order), never over a re-serialized `Value`. A
    // `Value` re-serializes in an order set by the `serde_json/preserve_order`
    // feature: key-sorted in a default-feature build of targo-trust, insertion
    // order in the compiler's crate graph (and under targo-trust's
    // `trust-mc-in-process`), which enables it through trust-mc's driver.
    // Hashing `metadata` therefore agreed with the compiler only by build
    // configuration, and refused every clean-kernel row in a standalone build
    // (KNOWN_HAZARDS, "A clean-kernel row can fail publication on a JSON
    // key-order skew"; DECISION_QUEUE CLEAN-CIC-TYPED-ADDRESS-1).
    // `trust_ir::ProofEvidence::CleanCic` holds no `Value` and no map at any
    // depth, so this encoding is the same under either feature, and it is the
    // byte string the compiler hashes (`to_vec` of `to_value(evidence)` in its
    // insertion-order graph). The round trip above already pins `metadata` to
    // exactly this typed value, so the digest binds the carried certificate.
    let Ok(bytes) = serde_json::to_vec(&decoded) else {
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

/// An observation cannot supply proof authority or repair a missing artifact.
/// Legacy proofs carry no diagnostics. A replayed proof may additionally carry
/// exactly the compiler's bounded informational observation matching its VC
/// snapshot and proof. Full current function/target/typed-row identity remains
/// bound by the original live compiler receipt, never by this diagnostic check.
/// Every other diagnostic still withholds this structural publication shape.
fn clean_cic_replay_diagnostic_matches(
    result: &VerificationResult,
    proof: &TransportProofEvidence,
    evidence: &trust_ir::ProofEvidence,
) -> bool {
    let [diagnostic] = proof.diagnostics.as_slice() else {
        return proof.diagnostics.is_empty();
    };
    if diagnostic.code != "clean_kernel_replay_audit_v1"
        || diagnostic.severity != trust_types::TransportEvidenceDiagnosticSeverity::Info
        || diagnostic.message
            != "Observed reuse of this admitted kernel proof; diagnostic data, not authority"
    {
        return false;
    }
    #[derive(serde::Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Observation {
        version: u32,
        subject: String,
        obligation_id: String,
        claim_digest_sha256: String,
        replay: serde_json::Value,
    }
    let Some(observation) = diagnostic
        .detail
        .as_deref()
        .filter(|detail| detail.len() <= 4096)
        .and_then(|detail| serde_json::from_str::<Observation>(detail).ok())
    else {
        return false;
    };
    let Some(structured) = structured_transport_evidence(result) else {
        return false;
    };
    let (Some(id), Some(claim), Some(snapshot)) = (
        structured.obligation_id.as_deref(),
        structured.claim_digest_sha256.as_deref(),
        structured.original_vc_snapshot.as_deref(),
    ) else {
        return false;
    };
    if observation.version != 1
        || observation.obligation_id != id
        || observation.claim_digest_sha256 != claim
    {
        return false;
    }
    let Ok(vc) = snapshot.decode_for_row(id, claim) else {
        return false;
    };
    observation.subject == vc.function.as_str()
        && trust_certify::proof_artifacts::ReplayAudit::matches_serialized_observation(
            &observation.replay,
            &vc,
            evidence,
        )
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
        || source_clause::proof_evidence_report(result, structured.as_ref(), materialization_root)
            .is_some()
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
    // The predicate above already required the transported evidence to AGREE
    // with the strength under the canonical legacy mapping; publish the
    // canonical spelling so the emitted report satisfies trust-types'
    // saved-report contract (`evidence == ProofEvidence::from(strength)`)
    // exactly, whichever spelling the compiler transported.
    let evidence = proof.evidence.as_ref().map(canonical_transport_proof_evidence)?;
    Some(PublishableNativeProofComponents { proof, native_trust_ir, strength, evidence })
}

/// The canonical spelling of a transported `ProofEvidence` record.
///
/// `ProofEvidence` is the newer evidence model and `ProofEvidence::from(
/// ProofStrength)` is its ONE documented mapping from the legacy assurance
/// ladder (`Sound` -> `SmtBacked`, `Heuristic` -> `Unchecked`, everything else
/// verbatim). The compiler's clean-kernel lane builds its evidence through that
/// mapping; its native trust-mc/trust-vc lane (`trust_verify.rs`,
/// `native_transport_proof_evidence`) copied `strength.assurance` verbatim
/// instead, so a PDR/CHC/SMT proof arrived spelled `{Pdr, Sound}` where the
/// contract expects `{Pdr, SmtBacked}`. Both spellings name the SAME rung of
/// the ladder (`AssuranceLevel::strength_order` is 2 for both); re-applying the
/// mapping is idempotent on already-canonical evidence and can never raise
/// standing (`Sound`/`SmtBacked` -> `SmtBacked`; `Trusted`, `Certified`,
/// `BoundedSound` are fixed points).
///
/// KR0 switch: the kernel stamp (`kernel_theory`, `env_digest`) is carried
/// through unchanged. It is not part of the strength mapping, so a stamped
/// record never agrees with a bare strength
/// (`transport_evidence_agrees_with_strength`), and the envelope copy of a
/// clean-kernel row keeps the theory id the published record names.
fn canonical_transport_proof_evidence(evidence: &ProofEvidence) -> ProofEvidence {
    let mut canonical = ProofEvidence::from(ProofStrength {
        reasoning: evidence.reasoning.clone(),
        assurance: evidence.assurance.clone(),
    });
    canonical.kernel_theory = evidence.kernel_theory;
    canonical.env_digest = evidence.env_digest;
    canonical
}

/// Whether a transported evidence record is the SAME claim as its strength
/// record: equal after both are taken through the one canonical mapping. This
/// is the exact loosening of `evidence == ProofEvidence::from(strength)`: a
/// different reasoning kind, or an assurance on a different rung (`Certified`
/// against `Sound`, `Trusted` against `Sound`, a bounded depth against an
/// unbounded strength), still disagrees and the row is still withheld.
fn transport_evidence_agrees_with_strength(
    evidence: &ProofEvidence,
    strength: &ProofStrength,
) -> bool {
    canonical_transport_proof_evidence(evidence) == ProofEvidence::from(strength.clone())
}

fn native_transport_evidence(
    structured: &crate::types::StructuredTransportEvidence,
) -> Option<ObligationTransportEvidenceReport> {
    (structured.obligation_id.is_some()
        || structured.identity.is_some()
        || structured.claim_digest_sha256.is_some()
        || structured.original_vc_snapshot.is_some()
        || structured.typed_kind.is_some()
        || structured.native_trust_ir.is_some()
        || structured.proof_evidence.is_some()
        || structured.monitor.is_some())
    .then(|| ObligationTransportEvidenceReport {
        identity: structured.identity.clone(),
        obligation_id: structured.obligation_id.clone(),
        claim_digest_sha256: structured.claim_digest_sha256.clone(),
        original_vc_snapshot: structured.original_vc_snapshot.clone(),
        typed_kind: structured.typed_kind.clone(),
        native_trust_ir: structured.native_trust_ir.clone(),
        // The transport envelope copy must reproduce the published proof
        // record exactly (trust-types `matching_transport_evidence_defect`),
        // and the published record carries the canonical evidence spelling —
        // so the envelope's `evidence` is taken through the same mapping. Only
        // that one field is rewritten; strength, identity, artifacts and
        // diagnostics stay the compiler's literal transport.
        proof_evidence: structured.proof_evidence.clone().map(|mut proof| {
            proof.evidence = proof.evidence.as_ref().map(canonical_transport_proof_evidence);
            proof
        }),
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
    // Historical formula-only WP remains diagnostic. Only the shared modern
    // body-certificate validator may admit WP at this publication boundary.
    let modern_wp = canonical_suite == "trust-wp"
        && proof.strength.as_ref().zip(proof.evidence.as_ref()).is_some_and(
            |(strength, evidence)| {
                trust_types::modern_body_wp_proof_defect(
                    &proof.artifacts,
                    obligation_id,
                    proof.request_id.as_deref(),
                    proof.proof_id.as_deref(),
                    strength,
                    evidence,
                    native_trust_ir,
                    materialization_root,
                )
                .is_none()
            },
        );
    let canonical_identity =
        matches!(canonical_suite.as_str(), "trust-mc" | "trust-vc" | "trust-wp")
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
    let binding_matches_native_id = if canonical_suite == "trust-wp" {
        modern_wp
    } else {
        proof.native_id.as_deref().is_some_and(|native_id| {
            proof.artifacts.iter().all(|artifact| {
                artifact
                    .materialization
                    .as_ref()
                    .is_none_or(|materialization| materialization.proof_binding_id == native_id)
            })
        })
    };
    let proof_topology_valid = if canonical_suite == "trust-wp" {
        modern_wp
    } else {
        materialization_root.map_or_else(
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
        )
    };
    let native_shape_valid = if canonical_suite == "trust-wp" {
        modern_wp
    } else {
        materialization_root.map_or_else(
            || native_trust_ir_artifact_shape_is_publishable(native_trust_ir),
            |root| native_trust_ir_artifact_shape_is_publishable_at_root(native_trust_ir, root),
        )
    };
    result.outcome.is_proved()
        && proof.status == TransportProofStatus::Proved
        && canonical_identity
        && proof.backend.trim().eq_ignore_ascii_case(&canonical_suite)
        && binding_matches_native_id
        && proof.strength.as_ref().is_some_and(proof_strength_is_publication_grade)
        && proof.evidence.as_ref().is_some_and(proof_evidence_is_publication_grade)
        && proof.strength.as_ref().is_some_and(|strength| {
            proof
                .evidence
                .as_ref()
                .is_some_and(|evidence| transport_evidence_agrees_with_strength(evidence, strength))
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
    let result = transport_to_verification_result("<typed-transport>", transport, None, None);
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

/// Trust: apply the canonical Clean CIC publication contract to typed compiler
/// transport, without requiring a native solver envelope or transcript.
pub(crate) fn transport_obligation_has_publishable_clean_cic_proof(
    transport: &trust_types::TransportObligationResult,
) -> bool {
    let result = transport_to_verification_result("<typed-transport>", transport, None, None);
    transport
        .proof_evidence
        .as_ref()
        .is_some_and(|proof| clean_cic_transport_proof_is_publishable(&result, proof))
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
        // Trust (coroutine resume-state contract): the published exported-
        // contract row. Same rationale as the assumption arm above — it is
        // conditional evidence, not a runtime-checked obligation, and folding
        // it to `Assertion` would give it a runtime fallback nothing enforces.
        // `UnsupportedMir` has no runtime fallback, so the row can never be
        // relabeled `RuntimeChecked`.
        s if s == trust_types::assumption::COROUTINE_RESUME_CONTRACT_ROW_KIND => {
            Some(VcKind::UnsupportedMir { kind: s.to_string(), detail: description.to_string() })
        }
        // Trust (2026-09-16): the global-alloc dealloc contract rows are conditional
        // evidence too (discharged) or an unproved premise (refused); neither may
        // acquire a runtime fallback. `UnsupportedMir` has none.
        s if s == trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND
            || s == trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_REFUSED_ROW_KIND =>
        {
            Some(VcKind::UnsupportedMir { kind: s.to_string(), detail: description.to_string() })
        }
        // Trust (D2 part B): a row whose formula consumed the coroutine
        // resume-state entry `Assume`. Same rationale as the two arms above,
        // and load-bearing here: the row's ORIGINAL kind survives after the
        // prefix (`…:assert`), so without this arm it would fall through and
        // could be folded back to `Assertion` — handing conditional evidence a
        // runtime fallback nothing enforces, which is how it would re-acquire a
        // `RuntimeChecked` relabel. `UnsupportedMir` has no runtime fallback.
        s if trust_types::assumption::is_coroutine_resume_conditional_row_kind(s) => {
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

/// The label the terminal listing prints for a row of kind `kind`, outcome
/// `outcome` and, for a `failed` row, failure basis `basis`. One function, so
/// the listing and the changed-only view (`crate::agent_delta`, reading
/// `ObligationRecord::listing_label`) print the same word for a row.
pub(crate) fn listing_label(
    kind: &str,
    outcome: VerificationOutcome,
    basis: Option<trust_types::FailureBasis>,
) -> String {
    // Trust (green front door, Stage 2): an `assumption:*` row is a recorded
    // unverified assumption, not an outcome the solver returned — render it as
    // ASSUMED so the terminal never displays it as UNKNOWN (or, for a defective
    // row, as PROVED). Display-only: the wire `VerificationOutcome` is
    // untouched, and the partition still counts a defective row as unknown.
    if kind.starts_with("assumption:") {
        "ASSUMED".to_string()
    } else if kind == trust_types::assumption::COROUTINE_RESUME_CONTRACT_ROW_KIND {
        // A published exported contract (verified-modulo-callers), not a solver
        // outcome — render it as such rather than UNKNOWN (or, for a defective
        // row, PROVED). Display-only, like ASSUMED above: the partition still
        // counts a defective row as unknown.
        "CONTRACT".to_string()
    } else if trust_types::assumption::is_coroutine_resume_conditional_row_kind(kind) {
        // Trust (D2 part B): discharged under the coroutine resume-state entry
        // assumption — conditional evidence, never an unconditional proof.
        // Display-only, like the two labels above.
        "CONDITIONAL".to_string()
    } else if let Some(basis) =
        basis.filter(|basis| outcome == VerificationOutcome::Failed && !basis.is_refuted())
    {
        // Nothing refuted this row; it fails closed. Display-only, like the
        // labels above: the outcome stays `failed` and the partition and gate
        // count it exactly as before.
        format!("FAILED: {}", basis.human_label())
    } else {
        outcome.label().to_string()
    }
}

/// Whether the listing labels `label` a plain proof: `PROVED`, not `ASSUMED`,
/// `CONTRACT`, `CONDITIONAL` or any outcome that is not a proof. The
/// changed-only view (`crate::agent_delta`) keeps every other row in sight on
/// every run.
pub(crate) fn listing_label_is_plain_proof(label: &str) -> bool {
    label == VerificationOutcome::Proved.label()
}

fn terminal_result_line(result: &VerificationResult) -> String {
    terminal_result_line_and_label(result).0
}

/// A row's listing line and the label it carries.
fn terminal_result_line_and_label(result: &VerificationResult) -> (String, String) {
    let label = listing_label(&result.kind, result.outcome, result.failure_basis());
    let line = format!(
        "  [{label}] [{}] {}{}",
        result.kind,
        result.message,
        terminal_result_detail_suffix(result)
    );
    (line, label)
}

/// How many of the rows the outcome partition counts `failed` nothing refuted
/// ([`trust_types::FailureBasis::UnprovedFailClosed`]). The partition is run over
/// exactly those rows, so the count can only ever be a subset of what the
/// partition (and therefore the gate) calls `failed`.
fn failed_unproved_rows(results: &[VerificationResult]) -> usize {
    let unproved: Vec<VerificationResult> = results
        .iter()
        .filter(|result| {
            result.failure_basis() == Some(trust_types::FailureBasis::UnprovedFailClosed)
        })
        .cloned()
        .collect();
    crate::pipeline::hardened::partition_outcome_counts(&unproved).0.failed
}

/// The terminal line that splits the `Summary:` line's `failed` count, or `None`
/// when every failed row was refuted.
fn failed_unproved_terminal_line(results: &[VerificationResult], failed: usize) -> Option<String> {
    let unproved = failed_unproved_rows(results);
    (unproved > 0).then(|| {
        format!(
            "Failed rows: {failed} failed, {unproved} of them unproved with NO counterexample: \
             nothing refuted them; they fail closed because Trust could not prove an unsafe \
             operation or a Level-0 safety/panic-freedom obligation it may not let pass (e.g. \
             a call it does not model, an `unwrap`/`expect`, an open generic dispatch, or a \
             function that did not lower to native trust-ir). The gate counts them as failed \
             either way."
        )
    })
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

fn discovered_unsafe_memory_repo_root(
    request: &UnsafeMemoryReportRequest,
) -> io::Result<(PathBuf, PathBuf)> {
    let requested_root = request.repo_root.canonicalize()?;
    let repo_root =
        crate::controlled_git::resolve_repo_root(&requested_root).map_err(io::Error::other)?;
    Ok((requested_root, repo_root))
}

fn require_exact_unsafe_memory_repo_root(
    requested_root: &Path,
    repo_root: &Path,
) -> io::Result<()> {
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
    Ok(())
}

fn unsafe_memory_repo_root(request: &UnsafeMemoryReportRequest) -> io::Result<PathBuf> {
    let (requested_root, repo_root) = discovered_unsafe_memory_repo_root(request)?;
    require_exact_unsafe_memory_repo_root(&requested_root, &repo_root)?;
    Ok(repo_root)
}

fn invalidate_previous_unsafe_memory_wrapper(
    request: &UnsafeMemoryReportRequest,
    output_dir: &Path,
) -> io::Result<()> {
    invalidate_previous_unsafe_memory_wrapper_with_hook(request, output_dir, || Ok(()))
}

fn invalidate_previous_unsafe_memory_wrapper_with_hook<F: FnOnce() -> io::Result<()>>(
    request: &UnsafeMemoryReportRequest,
    output_dir: &Path,
    before_unlink: F,
) -> io::Result<()> {
    // A nested request still identifies a repository: validate its output and
    // clear stale evidence before refusing the non-root request.
    let (requested_root, repo_root) = discovered_unsafe_memory_repo_root(request)?;
    if !existing_report_output_root_is_safe(output_dir)? {
        return require_exact_unsafe_memory_repo_root(&requested_root, &repo_root);
    }
    let output_root = output_dir.canonicalize()?;
    #[cfg(unix)]
    let opened_output = {
        use std::os::unix::fs::OpenOptionsExt as _;
        std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW)
            .open(&output_root)?
    };
    validated_output_exclusion(&repo_root, &output_root)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        let opened = opened_output.metadata()?;
        let current = std::fs::symlink_metadata(&output_root)?;
        if current.file_type().is_symlink()
            || !current.is_dir()
            || (opened.dev(), opened.ino()) != (current.dev(), current.ino())
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "unsafe-memory report output directory changed during wrapper invalidation",
            ));
        }
        before_unlink()?;
        unlink_previous_unsafe_memory_wrapper_at(&opened_output)?;
        require_exact_unsafe_memory_repo_root(&requested_root, &repo_root)
    }
    #[cfg(not(unix))]
    {
        before_unlink()?;
        remove_path_if_exists(
            &unsafe_memory_report_artifact_path(&output_root),
            "previous unsafe-memory report",
        )?;
        sync_directory(&output_root)?;
        require_exact_unsafe_memory_repo_root(&requested_root, &repo_root)
    }
}

#[cfg(unix)]
fn unlink_previous_unsafe_memory_wrapper_at(output_dir: &std::fs::File) -> io::Result<()> {
    use std::os::fd::AsRawFd as _;

    let name = std::ffi::CString::new(PROOF_UNSAFE_MEMORY_WRAPPER_FILE)
        .expect("fixed wrapper file name contains no NUL");
    // The directory descriptor, not a re-resolved path, selects the entry to remove.
    if unsafe { libc::unlinkat(output_dir.as_raw_fd(), name.as_ptr(), 0) } != 0 {
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::NotFound {
            return Err(error);
        }
    }
    output_dir.sync_all()
}

fn preflight_unsafe_memory_report(
    request: &UnsafeMemoryReportRequest,
    report: &VerificationReport,
    authorized_rows: &AuthorizedRows<'_>,
) -> io::Result<UnsafeMemoryReportPreflight> {
    let repo_root = unsafe_memory_repo_root(request)?;
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

    let coverage = unsafe_memory_coverage(report, authorized_rows)?;
    Ok(UnsafeMemoryReportPreflight { repo_root, candidate_commit, candidate_tree, coverage })
}

impl UnsafeMemoryReportPreflight {
    fn revalidate_source_snapshot(&self, report_output_root: Option<&Path>) -> io::Result<()> {
        let commit = git_stdout(&self.repo_root, &["rev-parse", "HEAD"])?;
        let tree = git_stdout(&self.repo_root, &["rev-parse", "HEAD^{tree}"])?;
        let output_exclusion = report_output_root
            .map(|output_root| validated_output_exclusion(&self.repo_root, output_root))
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
}

fn validated_output_exclusion(repo_root: &Path, output_root: &Path) -> io::Result<Option<String>> {
    let repo_root = repo_root.canonicalize()?;
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
    let tracked_pathspec = format!(":(top,literal){relative}");
    let tracked = crate::controlled_git::text_with_explicit_pathspec_magic(
        &repo_root,
        &["ls-files", "--", &tracked_pathspec],
        "unsafe-memory report tracked output probe",
        64 * 1024 * 1024,
        Duration::from_secs(30),
    )
    .map_err(io::Error::other)?;
    if !tracked.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "unsafe-memory report output must not contain tracked source files",
        ));
    }
    Ok(Some(relative.replace('\\', "/")))
}

fn unsafe_memory_coverage(
    report: &VerificationReport,
    authorized_rows: &AuthorizedRows<'_>,
) -> io::Result<ProofUnsafeMemoryCoverage> {
    let mut total = 0_u64;
    let mut proved = 0_u64;
    let mut blockers = Vec::new();
    // Emitted-row integrity only; the source-policy census is still unavailable.
    let mut seen_obligation_ids = BTreeSet::new();

    for (index, result) in report.results.iter().enumerate() {
        if !is_unsafe_memory_result(result) {
            continue;
        }
        total += 1;
        let owner = result.function.trim();
        if owner.is_empty() || owner.eq_ignore_ascii_case("unknown") {
            blockers.push(format!("unsafe-memory result {} has no function owner", result.kind));
            continue;
        }
        let structured = structured_transport_evidence(result);
        let Some(obligation_id) = structured
            .as_ref()
            .and_then(|evidence| evidence.obligation_id.as_deref())
            .map(str::trim)
            .filter(|id| !id.is_empty())
        else {
            blockers.push(format!("{owner}:{} lacks a structured obligation id", result.kind));
            continue;
        };
        if !seen_obligation_ids.insert(obligation_id.to_string()) {
            blockers.push(format!("duplicate unsafe-memory obligation id `{obligation_id}`"));
            continue;
        }
        if unsafe_memory_result_has_forbidden_marker(result) {
            blockers.push(format!(
                "{}:{} contains manual/stub/demo evidence markers",
                report_function_name(result),
                result.kind
            ));
            continue;
        }

        let structurally_publishable = publishable_native_proof_components(
            result,
            structured.as_ref(),
            report.proof_artifact_root.as_deref(),
        )
        .is_some();
        // Always `Some` before this point: `render_with_unsafe_memory_report`
        // returns `Err` when the report is unauthorized, and it is the only
        // caller of the preflight. The type now carries that.
        let live_authorized = authorized_rows.authorizes_proved_row(index, result);
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
    write_report_artifacts_from_root(report, output_dir, html_report, None, None, None).map(|_| ())
}

#[cfg(test)]
fn write_report_artifacts_from_root(
    report: &trust_types::JsonProofReport,
    output_dir: &Path,
    html_report: &str,
    source_root: Option<&Path>,
    unsafe_memory_preflight: Option<UnsafeMemoryReportPreflight>,
    sealed_canonical_json: Option<&[u8]>,
) -> io::Result<EvidenceBundleStatus> {
    write_report_artifacts_from_root_with_compiler_resources(
        report,
        output_dir,
        html_report,
        source_root,
        unsafe_memory_preflight,
        sealed_canonical_json,
        CompilerResourceReports::default(),
    )
}

fn write_report_artifacts_from_root_with_compiler_resources(
    report: &trust_types::JsonProofReport,
    output_dir: &Path,
    html_report: &str,
    source_root: Option<&Path>,
    unsafe_memory_preflight: Option<UnsafeMemoryReportPreflight>,
    sealed_canonical_json: Option<&[u8]>,
    resources: CompilerResourceReports<'_>,
) -> io::Result<EvidenceBundleStatus> {
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
    let mut evidence_bundle = persist_report_artifact_store(
        report,
        source_root,
        staged.path(),
        ArtifactStorePolicy::current(),
    )?;
    // The canonical bytes first: the bounds on the two derived renderings below
    // are derived from them.
    let owned_canonical_json;
    let canonical_json = if let Some(serialized) = sealed_canonical_json {
        serialized
    } else {
        owned_canonical_json = serialize_canonical_report_bounded(report)?;
        &owned_canonical_json
    };
    trust_report::write_ndjson_report(report, staged.path()).map_err(|error| {
        io::Error::new(error.kind(), format!("failed to stage NDJSON report: {error}"))
    })?;
    let ndjson_path = report_artifact_path(staged.path(), ReportArtifact::Ndjson);
    let ndjson_len = std::fs::metadata(&ndjson_path)?.len();
    // The NDJSON is bounded as a WRITE-side artifact, not as a reader's slurp:
    // nothing reads it back (the bounded readers all consume the canonical
    // report.json), and it is line-oriented, so a future reader streams it under
    // MAX_CARGO_JSON_LINE_BYTES. Applying the reader bound here threw away the
    // entire evidence of a successful 26,951-obligation run on 2026-09-10, and a
    // flat 2 GiB write bound threw away aterm-gui's complete 253,066-obligation
    // run on 2026-10-16. The bound is now derived from the canonical report
    // (`max_saved_ndjson_report_bytes`), and crossing it OMITS the rendering:
    // the run's report.json is never discarded for a derived artifact's size.
    let ndjson_bound = saved_ndjson_report_bound(canonical_json.len());
    if ndjson_len > ndjson_bound {
        std::fs::remove_file(&ndjson_path).map_err(|error| {
            io::Error::new(error.kind(), format!("failed to drop oversized NDJSON report: {error}"))
        })?;
        evidence_bundle.skipped_renderings.push(SkippedReportRendering {
            artifact: ReportArtifact::Ndjson.file_name(),
            bytes: ndjson_len,
            bound_bytes: ndjson_bound,
        });
    }
    // HTML is a human rendering of the same report: over its bound it is SKIPPED
    // with a note, never fatal (it used to fail the whole bundle, discarding
    // report.json and report.ndjson with it).
    let html_bound = saved_html_report_bound();
    if html_report.len() as u64 > html_bound {
        evidence_bundle.skipped_renderings.push(SkippedReportRendering {
            artifact: ReportArtifact::Html.file_name(),
            bytes: html_report.len() as u64,
            bound_bytes: html_bound,
        });
    } else {
        std::fs::write(report_artifact_path(staged.path(), ReportArtifact::Html), html_report)
            .map_err(|error| {
                io::Error::new(error.kind(), format!("failed to stage HTML report: {error}"))
            })?;
    }
    std::fs::write(report_artifact_path(staged.path(), ReportArtifact::Json), canonical_json)
        .map_err(|error| {
            io::Error::new(error.kind(), format!("failed to stage JSON report: {error}"))
        })?;
    if let Some(Err(error)) = resources.memory.map(|observations| {
        crate::compiler_memory::write_sidecar(staged.path(), canonical_json, observations)
    }) {
        // A missing observation is unknown, never a zero or proof gap.
        // Do not retain a partial sidecar or discard a completed verdict
        // merely because these diagnostic counters could not be saved.
        remove_path_if_exists(
            &staged.path().join(crate::compiler_memory::FILE_NAME),
            "incomplete compiler memory observations",
        )?;
        eprintln!("targo trust: warning: compiler memory observations unavailable: {error}");
    }
    if let Some(admission) = resources.admission {
        admission.write(staged.path(), canonical_json)?;
    }
    // The wrapper is a clean-source, release-shaped assertion bound to
    // report.json's hash. It must never stand over a bundle whose evidence is
    // incomplete, so it is withheld (and an earlier wrapper is not kept: the
    // commit below backs it up with the rest of the previous bundle and does
    // not reinstall it).
    let unsafe_memory_wrapper = match unsafe_memory_preflight.as_ref() {
        None => EvidenceBundleWrapper::NotRequested,
        Some(_) if !evidence_bundle.complete => EvidenceBundleWrapper::WithheldIncompleteBundle,
        Some(_) => EvidenceBundleWrapper::Written,
    };
    write_evidence_bundle_sidecar(
        &evidence_bundle,
        canonical_json,
        unsafe_memory_wrapper,
        staged.path(),
    )?;
    if let Some(preflight) = unsafe_memory_preflight.as_ref() {
        preflight.revalidate_source_snapshot(Some(&output_root))?;
        if unsafe_memory_wrapper == EvidenceBundleWrapper::Written {
            write_unsafe_memory_report_wrapper(preflight, staged.path())?;
        }
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
        if evidence_bundle
            .skipped_renderings
            .iter()
            .any(|skipped| skipped.artifact == artifact.file_name())
        {
            continue;
        }
        eprintln!("targo trust: wrote {}", report_artifact_path(&output_root, artifact).display());
    }
    for line in skipped_rendering_lines(&evidence_bundle, &output_root) {
        eprintln!("{line}");
    }
    eprintln!("targo trust: wrote {}", evidence_bundle_sidecar_path(&output_root).display());
    let memory_sidecar = output_root.join(crate::compiler_memory::FILE_NAME);
    if memory_sidecar.is_file() {
        eprintln!("targo trust: wrote {}", memory_sidecar.display());
    }
    if unsafe_memory_report_artifact_path(&output_root).is_file() {
        eprintln!(
            "targo trust: wrote {}",
            unsafe_memory_report_artifact_path(&output_root).display()
        );
    }
    if unsafe_memory_wrapper == EvidenceBundleWrapper::WithheldIncompleteBundle {
        eprintln!(
            "targo trust: WITHHELD {}: the evidence bundle is incomplete ({} artifact(s) not persisted), and an unsafe-memory assertion never stands over missing evidence",
            unsafe_memory_report_artifact_path(&output_root).display(),
            evidence_bundle.omitted_artifacts
        );
    }
    Ok(evidence_bundle)
}

fn report_evidence_artifacts(
    report: &trust_types::JsonProofReport,
) -> Vec<&TransportEvidenceArtifact> {
    let mut artifacts = Vec::new();
    for function in &report.functions {
        for obligation in &function.obligations {
            extend_obligation_evidence_artifacts(obligation, &mut artifacts);
        }
    }
    artifacts
}

/// The ONE walk over a row's evidence artifacts. The ambient-path refusal
/// (`report_contains_ambient_path_materializations`) and bundle persistence
/// (`path_backed_artifacts_in_persistence_order`) both use it, so an evidence
/// field added here is both checked and persisted (or recorded as omitted).
fn extend_obligation_evidence_artifacts<'a>(
    obligation: &'a trust_types::ObligationReport,
    artifacts: &mut Vec<&'a TransportEvidenceArtifact>,
) {
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

/// Whether a sealed report retains a path that names something the seal does
/// NOT bind.
///
/// The rule this enforces is "pathnames are mutable ambient state and cannot
/// survive inside a final publication capability". A content-addressed store
/// path is the one shape that is not ambient: it is
/// `<store>/sha256/<digest>`, its only variable component IS the declared
/// digest, and the digest is inside the seal. Such a path adds no authority to
/// the capability, so refusing it bought nothing — while forcing every artifact
/// inline, which is what made ay's report exceed 4 GiB and refused a release
/// after 4h36m of verification that had already succeeded.
///
/// Anything else — an absolute path, a relative path outside the fixed store,
/// a store path whose digest component disagrees with the declared digest — is
/// still ambient, and still refused.
fn report_contains_ambient_path_materializations(report: &trust_types::JsonProofReport) -> bool {
    report_evidence_artifacts(report).into_iter().any(|artifact| {
        let Some(materialization) = artifact.materialization.as_ref() else {
            return false;
        };
        if materialization.materialized_path.is_none() {
            return false;
        }
        // A path with no declared digest to derive it from is ambient by
        // definition: nothing in the seal pins what it points at.
        let Some(digest) = artifact.digest.as_ref() else {
            return true;
        };
        !materialization.path_is_digest_derived(digest)
    })
}

fn inline_artifact_materializations(
    artifacts: &mut [TransportEvidenceArtifact],
    source_root: &Path,
    total_bytes: &mut u64,
    still_path_backed: &mut usize,
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

        // BUDGET FIRST, and from the DECLARED length, so an artifact that will
        // not be inlined is never decoded and never held in memory at all.
        //
        // This aggregate used to be a hard error — "inline proof evidence
        // exceeds the N-byte aggregate limit; use --report-dir" — which is what
        // a 4h36m ay gate died on, and `--report-dir` did not help because the
        // seal runs before any output directory is known. Past the budget the
        // artifact now simply STAYS where it already is: a content-addressed
        // store entry at `<store>/sha256/<digest>`, which is where these bytes
        // lived before inlining copied them into the report as hex. Measured on
        // ay: inlined bytes were 58% of a 104 MB report for one small crate.
        // Count what LANDS IN THE REPORT, which is hex — two characters per
        // byte — not the decoded length. Budgeting the decoded size let twice
        // the intended volume through: measured on ay-arrays, 34 MB of
        // artifacts sailed under a 64 MiB budget and put 68.1 MB of hex in the
        // report, so the budget silently meant 128 MiB.
        let declared_len = artifact
            .materialization
            .as_ref()
            .expect("path-backed materialization checked")
            .byte_len;
        let projected = total_bytes.saturating_add(declared_len.saturating_mul(2));
        // T3 L4 (C06a): an artifact left path-backed by the inline budget is a CAP hit
        // (`trust_types::audit_ledger`; C11e3 takes the cap).
        if trust_types::audit_ledger::cap_hit_if(
            projected > max_inline_report_artifact_bytes(),
            "targo-trust/src/report.rs:MAX_INLINE_REPORT_ARTIFACT_BYTES",
        ) {
            *still_path_backed = still_path_backed.saturating_add(1);
            continue;
        }

        let bytes = artifact
            .materialization
            .as_ref()
            .expect("path-backed materialization checked")
            .decoded_bytes_at_root(&digest, source_root)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        // Charge the ENCODED size, matching the projection above.
        *total_bytes =
            total_bytes.checked_add((bytes.len() as u64).saturating_mul(2)).ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "inline report artifact byte overflow")
            })?;
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
) -> io::Result<usize> {
    let source_root = source_root.canonicalize().map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("could not canonicalize captured proof artifact root: {error}"),
        )
    })?;
    let mut total_bytes = 0_u64;
    let mut still_path_backed = 0_usize;
    for result in results {
        let Some(mut evidence) = structured_transport_evidence(result) else {
            continue;
        };
        if let Some(native) = &mut evidence.native_trust_ir {
            inline_artifact_materializations(
                &mut native.artifacts,
                &source_root,
                &mut total_bytes,
                &mut still_path_backed,
            )?;
        }
        if let Some(proof) = &mut evidence.proof_evidence {
            inline_artifact_materializations(
                &mut proof.artifacts,
                &source_root,
                &mut total_bytes,
                &mut still_path_backed,
            )?;
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
    // How many artifacts are STILL path-backed. The caller needs this because
    // the private artifact root must outlive the seal's credit evaluation
    // whenever any artifact remains in the store: every credit predicate
    // resolves such an artifact by re-reading and re-hashing the file through
    // that root.
    Ok(still_path_backed)
}

/// How a report bundle may persist path-backed proof evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ArtifactStorePolicy {
    /// Aggregate bytes that may be COPIED. Hard-linked artifacts cost neither
    /// a second copy nor copy time, so they are not charged.
    copy_cap_bytes: u64,
    /// Try to hard-link each artifact out of the run's private store first.
    link_from_private_store: bool,
}

impl ArtifactStorePolicy {
    const PRODUCTION: Self =
        Self { copy_cap_bytes: MAX_REPORT_ARTIFACT_STORE_BYTES, link_from_private_store: true };

    /// The production policy. Tests may lower the cap through a thread-local
    /// that exists only under `cfg(test)`: there is deliberately NO user-facing
    /// knob (env var or flag) that could change what a production bundle keeps.
    fn current() -> Self {
        #[cfg(test)]
        if let Some(policy) = test_hooks::ARTIFACT_STORE_POLICY.with(std::cell::Cell::get) {
            return policy;
        }
        Self::PRODUCTION
    }
}

#[cfg(test)]
mod test_hooks {
    use std::cell::Cell;

    thread_local! {
        pub(super) static ARTIFACT_STORE_POLICY: Cell<Option<super::ArtifactStorePolicy>> =
            const { Cell::new(None) };
        pub(super) static INLINE_BUDGET_BYTES: Cell<Option<u64>> = const { Cell::new(None) };
        pub(super) static SAVED_NDJSON_BOUND_BYTES: Cell<Option<u64>> = const { Cell::new(None) };
        pub(super) static SAVED_HTML_BOUND_BYTES: Cell<Option<u64>> = const { Cell::new(None) };
    }
}

/// Scope the existing thread-local storage policy for cross-owner tests only.
/// Nested calls and unwinding both restore the exact prior policy.
#[cfg(test)]
pub(crate) fn with_artifact_store_policy_for_test<R>(
    copy_cap_bytes: u64,
    link: bool,
    run: impl FnOnce() -> R,
) -> R {
    struct Restore(Option<ArtifactStorePolicy>);
    impl Drop for Restore {
        fn drop(&mut self) {
            test_hooks::ARTIFACT_STORE_POLICY.with(|cell| cell.set(self.0));
        }
    }
    let previous = test_hooks::ARTIFACT_STORE_POLICY.with(|cell| {
        cell.replace(Some(ArtifactStorePolicy { copy_cap_bytes, link_from_private_store: link }))
    });
    let _restore = Restore(previous);
    run()
}
/// Whether `--unsafe-memory` asked for a wrapper and whether it was written.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum EvidenceBundleWrapper {
    NotRequested,
    Written,
    /// Requested, but the bundle is incomplete: never written.
    WithheldIncompleteBundle,
}

/// One report row that references an omitted artifact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct OmittedArtifactRow {
    pub(crate) function: String,
    pub(crate) obligation_index: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) obligation_id: Option<String>,
    pub(crate) outcome: &'static str,
}

/// One unique (by digest) artifact the bundle did not persist.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct OmittedReportArtifact {
    pub(crate) digest_sha256: String,
    pub(crate) kind: String,
    pub(crate) byte_len: u64,
    /// Every row that references it, in report order. An omitted artifact
    /// behind an unknown or failed row leaves NO other trace on reload (only a
    /// proved row's missing evidence becomes a structural defect), so this
    /// list is the only record of it.
    pub(crate) rows: Vec<OmittedArtifactRow>,
}

/// What a saved report bundle actually holds of the run's path-backed
/// evidence. Serialized as `evidence-bundle.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct EvidenceBundleStatus {
    /// Every referenced path-backed artifact is in the bundle's own store.
    pub(crate) complete: bool,
    pub(crate) copy_cap_bytes: u64,
    pub(crate) persisted_artifacts: usize,
    pub(crate) persisted_bytes: u64,
    /// Persisted by hard link out of the run's private store (no second copy).
    pub(crate) linked_artifacts: usize,
    pub(crate) copied_artifacts: usize,
    /// Bytes charged against `copy_cap_bytes`.
    pub(crate) copied_bytes: u64,
    pub(crate) omitted_artifacts: usize,
    pub(crate) omitted_bytes: u64,
    /// Distinct rows (not row-artifact pairs) graded proved or runtime-checked
    /// with at least one omitted artifact. Such a
    /// row reloads with a structural evidence defect. Copy order puts these
    /// rows' artifacts first, so this is nonzero only when they alone overflow.
    pub(crate) omitted_proved_or_runtime_checked_rows: usize,
    pub(crate) omitted: Vec<OmittedReportArtifact>,
    /// Derived renderings of `report.json` (`report.ndjson`, `report.html`) that
    /// were not written because they crossed their size bound. A rendering's
    /// size never discards the report it renders; it is recorded here instead.
    /// Not evidence: `complete` is about proof artifacts and does not move.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub(crate) skipped_renderings: Vec<SkippedReportRendering>,
}

/// One derived rendering of the canonical report the bundle does not hold.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct SkippedReportRendering {
    pub(crate) artifact: &'static str,
    pub(crate) bytes: u64,
    pub(crate) bound_bytes: u64,
}

impl EvidenceBundleStatus {
    pub(crate) fn empty(copy_cap_bytes: u64) -> Self {
        Self {
            complete: true,
            copy_cap_bytes,
            persisted_artifacts: 0,
            persisted_bytes: 0,
            linked_artifacts: 0,
            copied_artifacts: 0,
            copied_bytes: 0,
            omitted_artifacts: 0,
            omitted_bytes: 0,
            omitted_proved_or_runtime_checked_rows: 0,
            omitted: Vec::new(),
            skipped_renderings: Vec::new(),
        }
    }
}

/// The `report.ndjson` bound for a canonical report of `canonical_report_bytes`
/// ([`crate::input_limits::max_saved_ndjson_report_bytes`]), or a test's own.
fn saved_ndjson_report_bound(canonical_report_bytes: usize) -> u64 {
    #[cfg(test)]
    if let Some(bound) = test_hooks::SAVED_NDJSON_BOUND_BYTES.with(std::cell::Cell::get) {
        return bound;
    }
    crate::input_limits::max_saved_ndjson_report_bytes(canonical_report_bytes) as u64
}

/// The `report.html` bound ([`crate::input_limits::MAX_SAVED_HTML_REPORT_BYTES`]),
/// or a test's own.
fn saved_html_report_bound() -> u64 {
    #[cfg(test)]
    if let Some(bound) = test_hooks::SAVED_HTML_BOUND_BYTES.with(std::cell::Cell::get) {
        return bound;
    }
    crate::input_limits::MAX_SAVED_HTML_REPORT_BYTES as u64
}

/// The human note for every rendering the bundle skipped, beside the `wrote`
/// lines of the artifacts it did write.
fn skipped_rendering_lines(status: &EvidenceBundleStatus, output_dir: &Path) -> Vec<String> {
    status
        .skipped_renderings
        .iter()
        .map(|skipped| {
            format!(
                "targo trust: SKIPPED {}: the rendering is {} bytes, over its {}-byte bound; it is \
                 a derived rendering of {}, which was written and carries every row (recorded in {})",
                output_dir.join(skipped.artifact).display(),
                skipped.bytes,
                skipped.bound_bytes,
                report_artifact_path(output_dir, ReportArtifact::Json).display(),
                evidence_bundle_sidecar_path(output_dir).display(),
            )
        })
        .collect()
}

#[derive(Serialize)]
struct EvidenceBundleSidecar<'a> {
    schema: &'static str,
    /// Binds this record to the exact report bytes it describes, so a sidecar
    /// from another run cannot be passed off as this one's.
    proof_report_path: &'static str,
    proof_report_hash: String,
    unsafe_memory_wrapper: EvidenceBundleWrapper,
    #[serde(flatten)]
    status: &'a EvidenceBundleStatus,
}

fn evidence_bundle_sidecar_path(output_dir: &Path) -> PathBuf {
    output_dir.join(REPORT_EVIDENCE_BUNDLE_FILE)
}

fn write_evidence_bundle_sidecar(
    status: &EvidenceBundleStatus,
    canonical_json: &[u8],
    unsafe_memory_wrapper: EvidenceBundleWrapper,
    staged_root: &Path,
) -> io::Result<()> {
    let sidecar = EvidenceBundleSidecar {
        schema: REPORT_EVIDENCE_BUNDLE_SCHEMA,
        proof_report_path: ReportArtifact::Json.file_name(),
        proof_report_hash: format!(
            "sha256:{}",
            trust_types::digest::lowercase_hex(&Sha256::digest(canonical_json))
        ),
        unsafe_memory_wrapper,
        status,
    };
    let json = serde_json::to_vec_pretty(&sidecar).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("failed to serialize {REPORT_EVIDENCE_BUNDLE_SCHEMA}: {error}"),
        )
    })?;
    std::fs::write(evidence_bundle_sidecar_path(staged_root), json).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!("failed to stage {REPORT_EVIDENCE_BUNDLE_FILE}: {error}"),
        )
    })
}

/// The `Result:` line of a run that exits 2 on the evidence gate (an
/// incomplete bundle where the run requires a complete one).
const EVIDENCE_GATE_FAILED_RESULT: &str = "Result: NOT PUBLISHED (report artifact evidence gate failed: the saved evidence bundle is incomplete and this run requires a complete one; it exits 2)";

/// The trust-report text summary of a run that exits 2 on the evidence gate,
/// with its sealed `Gate:` line relabelled so the sealed decision and exit
/// (possibly a pass with exit 0) never read as this run's outcome. The counts
/// are unchanged.
fn summary_with_overridden_gate(summary: &str) -> String {
    summary
        .lines()
        .map(|line| {
            let trimmed = line.trim_start();
            if let Some(rest) = trimmed.strip_prefix("Gate: ") {
                let indent = &line[..line.len() - trimmed.len()];
                format!(
                    "{indent}Sealed gate (OVERRIDDEN: this run exits 2 on the report artifact evidence gate): {rest}"
                )
            } else {
                line.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The disclosure printed next to the verdict when a bundle is incomplete.
/// Empty for a complete bundle.
pub(crate) fn evidence_bundle_incomplete_lines(
    status: &EvidenceBundleStatus,
    output_dir: &Path,
) -> Vec<String> {
    if status.complete {
        return Vec::new();
    }
    vec![
        format!(
            "targo trust: evidence bundle INCOMPLETE: {} artifact(s), {} byte(s) not persisted (report store copy cap {} bytes); {} from {} is not independently re-checkable",
            status.omitted_artifacts,
            status.omitted_bytes,
            status.copy_cap_bytes,
            ReportArtifact::Json.file_name(),
            output_dir.display()
        ),
        format!(
            "targo trust: the verdict above is this run's sealed verdict and is unchanged; {} proved/runtime-checked row(s) lost their saved evidence; every omitted artifact and the rows it backs are listed in {}",
            status.omitted_proved_or_runtime_checked_rows,
            evidence_bundle_sidecar_path(output_dir).display()
        ),
    ]
}

fn obligation_outcome_tag(outcome: &ObligationOutcome) -> &'static str {
    match outcome {
        ObligationOutcome::Proved { .. } => "proved",
        ObligationOutcome::Failed { .. } => "failed",
        ObligationOutcome::Unknown { .. } => "unknown",
        ObligationOutcome::RuntimeChecked { .. } => "runtime_checked",
        ObligationOutcome::Timeout { .. } => "timeout",
        ObligationOutcome::DesignRequirement { .. } => "design_requirement",
        // `#[non_exhaustive]`: a future outcome is recorded, never mistaken
        // for a favourable one (only "proved"/"runtime_checked" sort first).
        _ => "other",
    }
}

/// Path-backed artifacts in persistence order: every artifact of a proved or
/// runtime-checked row first, then the rest, each group in report order.
///
/// The order has a consumer: the native contract consumer rejects a bundle
/// with ANY structural defect, and only a proved row's missing evidence is
/// structural, so a partial bundle stays usable there exactly when the
/// favourable rows' artifacts fit.
fn path_backed_artifacts_in_persistence_order(
    report: &trust_types::JsonProofReport,
) -> Vec<ReportArtifactOccurrence<'_>> {
    let mut entries = Vec::new();
    let mut row_ordinal = 0usize;
    for function in &report.functions {
        for (obligation_index, obligation) in function.obligations.iter().enumerate() {
            let ordinal = row_ordinal;
            row_ordinal += 1;
            let row = OmittedArtifactRow {
                function: function.function.clone(),
                obligation_index,
                obligation_id: obligation.obligation_id.clone(),
                outcome: obligation_outcome_tag(&obligation.outcome),
            };
            let mut artifacts: Vec<&TransportEvidenceArtifact> = Vec::new();
            extend_obligation_evidence_artifacts(obligation, &mut artifacts);
            for artifact in artifacts {
                let path_backed = artifact
                    .materialization
                    .as_ref()
                    .and_then(|materialization| materialization.materialized_path.as_deref())
                    .is_some();
                if path_backed {
                    entries.push(ReportArtifactOccurrence {
                        row_ordinal: ordinal,
                        row: row.clone(),
                        artifact,
                    });
                }
            }
        }
    }
    artifact_occurrences_in_persistence_order(entries)
}

/// One observational artifact occurrence, with the row that references it.
/// Callers assign a unique ordinal to each logical row; repeated references
/// from that same row reuse its ordinal. This carries no live proof authority.
pub(crate) struct ReportArtifactOccurrence<'a> {
    /// The row's position in report order: its identity for counting (two
    /// functions may share a display name).
    pub(crate) row_ordinal: usize,
    pub(crate) row: OmittedArtifactRow,
    pub(crate) artifact: &'a TransportEvidenceArtifact,
}

fn artifact_row_is_favourable(row: &OmittedArtifactRow) -> bool {
    matches!(row.outcome, "proved" | "runtime_checked")
}

fn artifact_occurrences_in_persistence_order<'a>(
    occurrences: impl IntoIterator<Item = ReportArtifactOccurrence<'a>>,
) -> Vec<ReportArtifactOccurrence<'a>> {
    let mut entries = occurrences
        .into_iter()
        .filter(|entry| {
            entry
                .artifact
                .materialization
                .as_ref()
                .and_then(|materialization| materialization.materialized_path.as_deref())
                .is_some()
        })
        .collect::<Vec<_>>();
    // Stable: input/report order is kept inside each priority group.
    entries.sort_by_key(|entry| !artifact_row_is_favourable(&entry.row));
    entries
}

/// Persist typed occurrences under the existing fixed storage policy, without
/// constructing a report or minting proof authority. Inline artifacts need no
/// store entry. Proved/runtime-checked rows precede other rows, stably.
///
/// This writes the store only, not a report or sidecar. As with the report
/// adapter, use a fresh private staging directory and call once for the whole
/// bundle: a distinct destination's stale store is removed before writing.
pub(crate) fn persist_artifact_occurrences<'a>(
    occurrences: impl IntoIterator<Item = ReportArtifactOccurrence<'a>>,
    source_root: &Path,
    output_dir: &Path,
) -> io::Result<EvidenceBundleStatus> {
    persist_ordered_artifact_store(
        artifact_occurrences_in_persistence_order(occurrences),
        Some(source_root),
        output_dir,
        ArtifactStorePolicy::current(),
    )
}

/// What happened to the first occurrence of a digest.
enum PersistedDigest {
    Persisted { byte_len: u64 },
    Omitted { byte_len: u64, index: usize },
}

/// Persist every referenced path-backed proof materialization into the
/// report's own canonical SHA-256 store, so a saved report stays independently
/// re-checkable after the compiler's private run store disappears, and
/// diff/query resolve the same relative descriptors beneath report_dir.
///
/// Each artifact is first HARD-LINKED out of the private store (same
/// filesystem: no second copy, no copy time; the compiler publishes those
/// files write-once and the private store is deleted when the run ends), and
/// only copied when linking fails. Either way the bundle's file is re-read
/// and re-hashed against the declared digest. Copies are charged against
/// `policy.copy_cap_bytes`; an artifact that would cross the cap is OMITTED and
/// recorded — never a reason to discard the run's sealed verdict, because the
/// bundle is observational: a saved report never carries proof authority, and a
/// missing artifact reloads as an evidence defect that can only downgrade.
///
/// Real I/O and integrity failures (unreadable or tampered evidence, a
/// symlinked store, a failed write) remain hard errors.
fn persist_report_artifact_store(
    report: &trust_types::JsonProofReport,
    source_root: Option<&Path>,
    output_dir: &Path,
    policy: ArtifactStorePolicy,
) -> io::Result<EvidenceBundleStatus> {
    persist_ordered_artifact_store(
        path_backed_artifacts_in_persistence_order(report),
        source_root,
        output_dir,
        policy,
    )
}

fn persist_ordered_artifact_store(
    path_backed: Vec<ReportArtifactOccurrence<'_>>,
    source_root: Option<&Path>,
    output_dir: &Path,
    policy: ArtifactStorePolicy,
) -> io::Result<EvidenceBundleStatus> {
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

    let mut status = EvidenceBundleStatus::empty(policy.copy_cap_bytes);
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
        return Ok(status);
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

    let mut seen: BTreeMap<String, PersistedDigest> = BTreeMap::new();
    // Favourable rows already counted as having lost evidence: a ROW count, so
    // one row with several omitted artifacts counts once.
    let mut favourable_rows_with_omissions: BTreeSet<usize> = BTreeSet::new();
    // (omitted index, row ordinal) pairs already recorded: one row may carry
    // the same artifact in both its proof and its transport evidence.
    let mut recorded_omission_rows: BTreeSet<(usize, usize)> = BTreeSet::new();
    for ReportArtifactOccurrence { row_ordinal, row, artifact } in path_backed {
        let digest = artifact.digest.as_ref().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "path-backed report artifact has no declared digest",
            )
        })?;
        let materialization = artifact.materialization.as_ref().expect("filtered materialization");
        // Payload bytes and counters deduplicate; descriptor validity does
        // not. A later occurrence may bind the same bytes to a different row,
        // but must remain independently reloadable, even when cap-omitted.
        materialization
            .validate_path_descriptor(digest)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        let favourable = artifact_row_is_favourable(&row);

        if let Some(first) = seen.get(&digest.value) {
            // A repeated occurrence is not re-read (the first one was hashed),
            // but it must still declare the first occurrence's length: the
            // re-read this replaces is what used to catch a disagreeing
            // `byte_len` for the same digest.
            let (first_len, omitted_index) = match first {
                PersistedDigest::Persisted { byte_len } => (*byte_len, None),
                PersistedDigest::Omitted { byte_len, index } => (*byte_len, Some(*index)),
            };
            if materialization.byte_len != first_len {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "report artifact {} declares {} bytes but an earlier occurrence of the same digest declared {first_len}",
                        digest.value, materialization.byte_len
                    ),
                ));
            }
            if let Some(index) = omitted_index {
                if recorded_omission_rows.insert((index, row_ordinal)) {
                    status.omitted[index].rows.push(row);
                }
                if favourable {
                    favourable_rows_with_omissions.insert(row_ordinal);
                }
            }
            continue;
        }

        if !output_owns_store {
            // The bundle IS the source store: nothing to copy, only validate.
            materialization
                .decoded_bytes_at_root(digest, &source_root)
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
            status.persisted_artifacts += 1;
            status.persisted_bytes =
                status.persisted_bytes.saturating_add(materialization.byte_len);
            seen.insert(
                digest.value.clone(),
                PersistedDigest::Persisted { byte_len: materialization.byte_len },
            );
            continue;
        }

        let destination = destination_store.join(&digest.value);
        let linked = policy.link_from_private_store
            && link_private_artifact(materialization, digest, &source_root, &destination)?;
        if linked {
            // Re-read THROUGH THE BUNDLE: the bytes a later reader will see.
            if let Err(error) = materialization.decoded_bytes_at_root(digest, &output_root) {
                let _ = std::fs::remove_file(&destination);
                return Err(io::Error::new(io::ErrorKind::InvalidData, error));
            }
            status.linked_artifacts += 1;
        } else {
            let projected =
                status.copied_bytes.checked_add(materialization.byte_len).ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "report artifact byte count overflow",
                    )
                })?;
            // T3 L4 (C06a): an artifact the store cap omits is a CAP hit
            // (`trust_types::audit_ledger`; C11e3 takes the cap).
            if trust_types::audit_ledger::cap_hit_if(
                projected > policy.copy_cap_bytes,
                "targo-trust/src/report.rs:MAX_REPORT_ARTIFACT_STORE_BYTES",
            ) {
                // Omit, and keep going: a later, smaller artifact may still fit.
                status.omitted_bytes =
                    status.omitted_bytes.saturating_add(materialization.byte_len);
                if favourable {
                    favourable_rows_with_omissions.insert(row_ordinal);
                }
                recorded_omission_rows.insert((status.omitted.len(), row_ordinal));
                seen.insert(
                    digest.value.clone(),
                    PersistedDigest::Omitted {
                        byte_len: materialization.byte_len,
                        index: status.omitted.len(),
                    },
                );
                status.omitted.push(OmittedReportArtifact {
                    digest_sha256: digest.value.clone(),
                    kind: artifact.kind.clone(),
                    byte_len: materialization.byte_len,
                    rows: vec![row],
                });
                continue;
            }
            let bytes = materialization
                .decoded_bytes_at_root(digest, &source_root)
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
            let mut file = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&destination)
                .map_err(|error| {
                    io::Error::new(
                        error.kind(),
                        format!(
                            "could not create report proof artifact {}: {error}",
                            destination.display()
                        ),
                    )
                })?;
            file.write_all(&bytes)?;
            file.sync_all()?;
            status.copied_bytes = projected;
            status.copied_artifacts += 1;
        }
        status.persisted_artifacts += 1;
        status.persisted_bytes = status.persisted_bytes.saturating_add(materialization.byte_len);
        seen.insert(
            digest.value.clone(),
            PersistedDigest::Persisted { byte_len: materialization.byte_len },
        );
    }
    status.omitted_artifacts = status.omitted.len();
    status.omitted_proved_or_runtime_checked_rows = favourable_rows_with_omissions.len();
    status.complete = status.omitted.is_empty();
    if output_owns_store {
        sync_directory(&destination_store)?;
    }
    Ok(status)
}

/// Hard-link one artifact from the private run store into the bundle.
/// `Ok(false)` means "could not link, copy instead" (another filesystem, a
/// platform without hard links, a missing or odd source entry — the copy path
/// re-validates and reports the real error, if any).
fn link_private_artifact(
    materialization: &trust_types::TransportArtifactMaterialization,
    digest: &trust_types::TransportArtifactDigest,
    source_root: &Path,
    destination: &Path,
) -> io::Result<bool> {
    // Only `<store>/sha256/<declared digest>` — the same shape the seal admits.
    if !materialization.path_is_digest_derived(digest) {
        return Ok(false);
    }
    let Some(relative) = materialization.materialized_path.as_deref() else {
        return Ok(false);
    };
    let source = source_root.join(relative);
    match std::fs::symlink_metadata(&source) {
        Ok(metadata)
            if metadata.is_file()
                && !metadata.file_type().is_symlink()
                && metadata.len() == materialization.byte_len => {}
        _ => return Ok(false),
    }
    match std::fs::hard_link(&source, destination) {
        Ok(()) => Ok(true),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => Err(io::Error::new(
            error.kind(),
            format!("could not create report proof artifact {}: {error}", destination.display()),
        )),
        Err(_) => Ok(false),
    }
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
        evidence_bundle_sidecar_path(staged_root),
        staged_root.join(crate::compiler_memory::FILE_NAME),
        staged_root.join(crate::compiler_admission::FILE_NAME),
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

fn report_bundle_relative_paths() -> [PathBuf; 8] {
    [
        PathBuf::from(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY),
        PathBuf::from(ReportArtifact::Ndjson.file_name()),
        PathBuf::from(ReportArtifact::Html.file_name()),
        PathBuf::from(REPORT_EVIDENCE_BUNDLE_FILE),
        PathBuf::from(crate::compiler_memory::FILE_NAME),
        PathBuf::from(crate::compiler_admission::FILE_NAME),
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

/// The reason a canonical report row carries when the gate counted its transport
/// row as CONDITIONAL EVIDENCE rather than as an outcome (it becomes a fail-closed
/// `unknown` here, never proof credit).
///
/// Trust (2026-10-02, diag-vs-report): every such row used to say "declared
/// contract panic", including the `assumption:*` ledger rows the gate counts as
/// `assumed`. On trust-vc-types (survey 2026-10-02) the 17 `assumption:expected-
/// absent-callee` rows read in report.json as `unsupported_mir` "declared contract
/// panic" unknowns, and the 17 genuine timeouts were then mistaken for the gate's
/// 17 `assumed`. A row must say what the gate counted it as.
pub(crate) fn conditional_evidence_report_reason(declared_contract_panic: bool) -> &'static str {
    if declared_contract_panic {
        "declared contract panic (conditional policy row; no proof credit)"
    } else {
        "conditional evidence: an assumption-ledger or published-contract row the gate counts \
         as `assumed` (conditional policy row; no proof credit)"
    }
}

#[cfg(test)]
mod tests {
    include!("source_clause_publication_tests.rs");
    use std::fs;

    mod artifact_store_core;

    use trust_types::{
        TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX, TRUST_VC_PROOF_ARTIFACT_ID_PREFIX,
        TRUST_VC_PROOF_CERTIFICATE_URI_PREFIX,
    };

    use super::*;

    /// The inline budget is charged in HEX (two characters per decoded byte),
    /// so its floor must be twice the owner's 512 MiB DECODED cap; otherwise
    /// a report with 256-512 MiB of decoded evidence would keep store paths
    /// in the sealed JSON where main sealed it fully self-contained.
    #[test]
    fn the_inline_budget_floor_is_the_owners_decoded_cap_in_hex() {
        assert!(max_inline_report_artifact_bytes() >= 2 * MAX_INLINE_REPORT_ARTIFACT_BYTES);
    }

    /// The streamed receipt is the materialized receipt, byte for byte: the
    /// seal and every validation now stream, so a frame drift would not fail
    /// the seal-then-validate tests on its own. Pinned against the old
    /// materializing definition, with and without an artifact root, and the
    /// counting pass still refuses past its limit.
    #[test]
    fn the_streamed_publication_receipt_equals_the_materialized_one() {
        let state = serde_json::json!({
            "rows": [{"function": "f", "outcome": "proved", "bytes": "00ff".repeat(64)}],
            "subject": "crate-a",
            "total": 1,
        });
        let serialized = serde_json::to_vec(&state).expect("serialize state");
        let session = "a".repeat(64);
        for root in [None, Some(Path::new("/tmp/targo-proof-artifacts"))] {
            let streamed =
                streamed_complete_report_receipt("crate-a", &session, &state, root, u64::MAX)
                    .expect("stream receipt");
            assert_eq!(
                streamed,
                complete_report_receipt("crate-a", &session, &serialized, root),
                "streaming must feed the digest frame exactly the materialized bytes"
            );
        }
        let too_small = u64::try_from(serialized.len()).expect("len fits") - 1;
        assert!(
            streamed_complete_report_receipt("crate-a", &session, &state, None, too_small).is_err(),
            "the counting pass must refuse a state past its limit"
        );
    }
    use crate::types::transport_to_verification_result;

    /// The row-at-a-time comparison must decide EXACTLY what the two
    /// whole-vector `serde_json::to_vec` buffers decided. This asserts the two
    /// forms agree on every case, including the ones that could differ only in
    /// framing: empty vectors, a length mismatch either way, a difference in a
    /// trailing row, `None` vs `Some` on an optional field, and strings whose
    /// escaping changes their serialized length.
    #[test]
    fn the_row_at_a_time_projection_compare_decides_what_the_whole_buffer_compare_decided() {
        fn whole_buffer(left: &[VerificationResult], right: &[VerificationResult]) -> Option<bool> {
            Some(serde_json::to_vec(left).ok()? == serde_json::to_vec(right).ok()?)
        }

        let base = result_with_location(None);
        let spanned = result_with_location(Some(SourceSpan {
            file: "src/lib.rs".into(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 2,
        }));
        let mut reasoned = base.clone();
        reasoned.reason = Some("downgraded before publication".into());
        let mut escaped = base.clone();
        escaped.message = "quote \" backslash \\ newline \n tab \t \u{2603}".into();
        let mut other_outcome = base.clone();
        other_outcome.outcome = VerificationOutcome::Unknown;
        let mut long_raw = base.clone();
        long_raw.raw_line = "z".repeat(8192);

        let cases: Vec<(Vec<VerificationResult>, Vec<VerificationResult>)> = vec![
            (vec![], vec![]),
            (vec![], vec![base.clone()]),
            (vec![base.clone()], vec![]),
            (vec![base.clone()], vec![base.clone()]),
            (vec![base.clone()], vec![reasoned.clone()]),
            (vec![base.clone()], vec![spanned.clone()]),
            (vec![base.clone()], vec![other_outcome.clone()]),
            (vec![escaped.clone()], vec![escaped.clone()]),
            (vec![escaped.clone()], vec![base.clone()]),
            (
                vec![base.clone(), spanned.clone(), long_raw.clone()],
                vec![base.clone(), spanned.clone(), long_raw.clone()],
            ),
            (
                vec![base.clone(), spanned.clone(), long_raw.clone()],
                vec![base.clone(), spanned.clone(), reasoned.clone()],
            ),
            (
                vec![base.clone(), spanned.clone()],
                vec![base.clone(), spanned.clone(), long_raw.clone()],
            ),
            (
                vec![base.clone(), spanned.clone(), long_raw.clone()],
                vec![base.clone(), spanned.clone()],
            ),
        ];

        let mut agreed = 0usize;
        let mut equal_verdicts = 0usize;
        for (index, (left, right)) in cases.iter().enumerate() {
            let expected = whole_buffer(left, right);
            let actual = publication_projection_is_byte_identical(left, right);
            assert_eq!(expected, actual, "case {index} disagreed");
            if expected == Some(true) {
                equal_verdicts += 1;
            }
            agreed += 1;
        }
        // An all-`false` or all-`true` corpus would not exercise the compare.
        assert_eq!(agreed, 13, "every case must be decided");
        assert_eq!(equal_verdicts, 4, "both verdicts must be represented");
    }

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

    /// `row` with a stable obligation key (T9) bound into its structured
    /// evidence, as every compiler row carries one: `<function>#<id of (kind,
    /// nth)>`, package `test`.
    fn with_stable_key(mut row: VerificationResult, nth: u32) -> VerificationResult {
        let mut evidence = crate::types::structured_transport_evidence(&row).unwrap_or(
            crate::types::StructuredTransportEvidence {
                assumes: Vec::new(),
                obligation_id: None,
                claim_digest_sha256: None,
                original_vc_snapshot: None,
                typed_kind: None,
                design_mandate: false,
                runtime_checks: None,
                native_trust_ir: None,
                proof_evidence: None,
                monitor: None,
                identity: None,
                grade: None,
            },
        );
        evidence.identity = Some(trust_types::obligation_identity::ObligationIdentity {
            key: trust_types::obligation_identity::obligation_key(
                &row.function,
                &trust_types::obligation_identity::local_id(&row.kind, "none:test", nth),
            ),
            package: "test".to_string(),
            function_source_sha256: None,
            expanded_function_identity: None,
        });
        crate::types::replace_structured_transport_evidence(&mut row, &evidence)
            .expect("evidence serializes");
        row
    }

    fn full_verifier_result(outcome: VerificationOutcome) -> VerificationResult {
        with_stable_key(full_verifier_result_unkeyed(outcome), 0)
    }

    fn full_verifier_result_unkeyed(outcome: VerificationOutcome) -> VerificationResult {
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

    /// An unsupported-MIR row that CLAIMS proof gets no proof credit from the
    /// gate partition either. Three places already refuse it credit —
    /// `authorizes_proved_row`, the `unsupported_favorable` rewrite in
    /// `attach_live_transport_evidence`, and `report_vc_kind`'s no-fallback
    /// carrier — and `partition_outcome_counts`, which feeds the exit-code gate,
    /// was the one that still counted it `proved`. The gate then published a
    /// proof count the canonical projection would not back and the seal refused
    /// the run at its last step (ay's release gate, 2026-09-12, after 2.5 h).
    #[test]
    fn an_unsupported_mir_row_claiming_proof_gets_no_gate_proof_credit() {
        let claims_proof = full_verifier_result(VerificationOutcome::Proved);
        assert!(
            matches!(report_vc_kind(&claims_proof), VcKind::UnsupportedMir { .. }),
            "fixture must classify as unsupported MIR",
        );

        let (counts, defects) = crate::pipeline::hardened::partition_outcome_counts(
            std::slice::from_ref(&claims_proof),
        );
        assert_eq!(counts.proved, 0, "an unsupported-MIR row carries no proof credit");
        assert_eq!(counts.unknown, 1, "it is a genuine unknown");
        assert!(
            defects.iter().any(|defect| defect.contains("unsupported MIR")),
            "the downgrade must be reported as a transport defect, got: {defects:?}",
        );

        // End to end: the gate partition and the canonical projection agree, so
        // the report seals instead of refusing at the last step.
        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![claims_proof],
            Vec::new(),
        ));
        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_proved, 0);
        assert_eq!(canonical.summary.total_unknown, 1);
        assert_eq!(
            report.canonical_report_state_divergence(&canonical),
            None,
            "gate partition and canonical projection must agree row-for-row",
        );
    }

    /// A design mandate that TIMED OUT is still a design mandate.
    ///
    /// The gate counts a mandate on an `Unknown` OR `Timeout` row, and
    /// `to_trust_report` classifies an authorized one as a design requirement.
    /// `attach_live_transport_evidence` then overwrote every `Timeout` row's
    /// outcome unconditionally, erasing that classification — so a timed-out
    /// mandate counted in `mandated` for the gate and left
    /// `total_design_requirements` in the report. MEASURED on trust-wp
    /// 2026-09-13: 261 mandated against 227 design requirements, exactly the 34
    /// timed-out ones.
    ///
    /// The solver's time budget says nothing about an obligation's STATUS: a
    /// mandate is a deliberate non-discharge, whether the prover stopped at the
    /// first step or at the deadline.
    #[test]
    fn a_timed_out_design_mandate_keeps_its_classification() {
        assert!(
            matches!(VerificationOutcome::Timeout, VerificationOutcome::Timeout),
            "Timeout is one of the two inconclusive outcomes the gate counts as mandated",
        );

        let mandate_line =
            format!("targo-trust-structured-transport-evidence:{}", r#"{"design_mandate":true}"#,);
        // The same row twice, differing ONLY in which inconclusive outcome it
        // carries. The gate must bucket both identically.
        let mut unknown_mandate = full_verifier_result(VerificationOutcome::Unknown);
        unknown_mandate.kind = "hardened_process_semantics".into();
        unknown_mandate.raw_line = mandate_line.clone();
        let mut timeout_mandate = unknown_mandate.clone();
        timeout_mandate.outcome = VerificationOutcome::Timeout;

        for (label, row) in [("unknown", &unknown_mandate), ("timeout", &timeout_mandate)] {
            let (counts, _) =
                crate::pipeline::hardened::partition_outcome_counts(std::slice::from_ref(row));
            assert_eq!(counts.mandated, 1, "{label} mandate must count as mandated");
            assert_eq!(counts.unknown, 0, "{label} mandate is not a genuine unknown");
        }

        // Both are mandates to the gate, so both must be design requirements in
        // the canonical projection — the timeout must not demote one of them.
        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![unknown_mandate, timeout_mandate],
            Vec::new(),
        ));
        let canonical = report.to_trust_report();
        assert_eq!(
            canonical.summary.total_design_requirements, 2,
            "a timed-out design mandate must not be demoted to a plain Timeout",
        );
        assert!(
            !canonical
                .functions
                .iter()
                .flat_map(|function| &function.obligations)
                .any(|obligation| matches!(&obligation.outcome, ObligationOutcome::Timeout { .. })),
            "the timed-out mandate must not render as a Timeout: {:?}",
            canonical
                .functions
                .iter()
                .flat_map(|function| &function.obligations)
                .map(|obligation| &obligation.outcome)
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            report.canonical_report_state_divergence(&canonical),
            None,
            "gate and projection must agree on the mandate count",
        );
    }

    /// A row the gate counts as a design mandate must RESOLVE to a category, or
    /// the canonical report cannot label it a design requirement and it silently
    /// becomes an ordinary unknown. `transport_design_mandate` admitted a row
    /// through the TYPED payload's category or the `hardened_*` tag spelling,
    /// while the label was looked up from the tag alone — so a typed hardened VC
    /// with an ordinary tag counted for the gate and resolved to nothing for the
    /// report. MEASURED on trust-wp 2026-09-13:
    /// `total_design_requirements 227 != authorized_mandated 261`, 34 rows.
    #[test]
    fn a_mandate_the_gate_counts_always_resolves_to_a_category() {
        // A typed hardened VC: the typed path and the tag path must both resolve.
        let kind = VcKind::HardenedBoundary {
            category: HardenedVcCategory::ProcessSemantics,
            callee: "std::process::exit".into(),
            detail: "process semantics".into(),
        };
        let evidence = crate::types::StructuredTransportEvidence {
            assumes: Vec::new(),
            obligation_id: None,
            claim_digest_sha256: None,
            original_vc_snapshot: None,
            typed_kind: Some(Box::new(kind.clone())),
            design_mandate: true,
            runtime_checks: None,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            identity: None,
            grade: None,
        };
        let mut row = full_verifier_result(VerificationOutcome::Unknown);
        row.kind = kind.transport_tag();
        row.message = kind.description();
        row.raw_line = format!(
            "targo-trust-structured-transport-evidence:{}",
            serde_json::to_string(&evidence).expect("evidence serializes"),
        );

        assert!(transport_design_mandate(&row), "the gate admits this row as a design mandate",);
        assert!(
            hardened_mandate_category(&row).is_some(),
            "so a category MUST resolve for it — otherwise the canonical report \
             cannot label it and the two counts disagree",
        );

        // And the invariant itself: whatever the row, the predicate and the
        // category resolution answer together or not at all. The probes cover a
        // typed `HardenedBoundary` mandate, a plain full-verifier row with no
        // mandate at all, and main's real `[unsafe:unmodeled-call]` specimen — a
        // typed `Assertion` whose category comes from its MESSAGE, not its tag.
        for probe in [
            &row,
            &full_verifier_result(VerificationOutcome::Unknown),
            &failed_unmodeled_call_mandate_result(),
        ] {
            assert_eq!(
                transport_design_mandate(probe),
                hardened_mandate_category(probe).is_some(),
                "predicate and category must never disagree",
            );
        }
    }

    /// Every bucket the GATE assigns must survive into the canonical projection.
    /// Two rows broke this, each found only after a full seal + gate cycle:
    ///
    ///   * a FAILED row carrying the design-mandate bit — the gate counts it
    ///     `failed` (the outcome match runs before the mandate test, which only
    ///     sees Unknown/Timeout), while the projection labelled it a design
    ///     REQUIREMENT and it left `total_failed`. MEASURED on trust-wp:
    ///     `total_failed 1113 != 1185`, exactly 72 such rows.
    ///   * a FAILED `assumption:*` row — the gate counts it `assumed` and the
    ///     seal expects it among the canonical unknowns, while the projection
    ///     published it as a refutation.
    ///
    /// Both now ask the partition instead of re-deriving its rules.
    #[test]
    fn the_canonical_projection_keeps_every_bucket_the_gate_assigned() {
        let mandate_line =
            format!("targo-trust-structured-transport-evidence:{}", r#"{"design_mandate":true}"#,);

        // A FAILED row that carries the mandate bit is a FAILURE to the gate.
        let mut failed_mandate = full_verifier_result(VerificationOutcome::Failed);
        failed_mandate.kind = "hardened_process_semantics".into();
        failed_mandate.raw_line = mandate_line.clone();
        assert!(transport_design_mandate(&failed_mandate), "the bit is set");
        assert!(
            !crate::pipeline::hardened::counts_as_design_mandate(&failed_mandate),
            "a refuted row is counted `failed`, never as a design mandate",
        );
        let (counts, _) = crate::pipeline::hardened::partition_outcome_counts(
            std::slice::from_ref(&failed_mandate),
        );
        assert_eq!(counts.failed, 1);
        assert_eq!(counts.mandated, 0);

        // A FAILED assumption row is CONDITIONAL EVIDENCE to the gate, not a
        // refutation — it must not reach the canonical report as a failure.
        let mut failed_assumption = full_verifier_result(VerificationOutcome::Failed);
        failed_assumption.kind = "assumption:extern-call".into();
        let (counts, _) = crate::pipeline::hardened::partition_outcome_counts(
            std::slice::from_ref(&failed_assumption),
        );
        assert_eq!(counts.assumed, 1, "the gate counts it as an assumption");
        assert_eq!(counts.failed, 0, "and NOT as a refutation");
        assert!(
            crate::pipeline::hardened::counts_as_conditional_evidence(&failed_assumption),
            "so the canonical projection must carry it as conditional evidence",
        );
    }

    /// The REAL specimen shape behind the Failed-with-mandate question: an
    /// `[unsafe:unmodeled-call]` completeness row.
    ///
    /// `hardened_category()` maps `VcKind::Assertion` whose message starts with
    /// `[unsafe` to `UnsafeOperation`, and the compiler mints that VC with the
    /// always-SAT violation formula `Bool(true)`
    /// (`trust_verify.rs` — "Always SAT = always a finding: no model of this
    /// call's effects"). The transport constructor's mandate rule WAS
    /// `hardened_category().is_some() && matches!(formula, Bool(true))`, so the
    /// row carried `design_mandate: true` AND was REFUTED. Since
    /// G3-MANDATE-L1-ONLY-1 (2026-10-27) the compiler sets the bit only through
    /// `VcKind::is_hardened_design_mandate`, which refuses the L0
    /// `UnsafeOperation`/`FfiBoundary` categories, so a current compiler no longer
    /// emits this shape; the pin stays because the wire still admits the
    /// combination (an older compiler, a hand-made report). That combination is a
    /// finding, not a bucket the design owes: the owner's acceptance criterion
    /// for the mandate bucket is "inconclusive + the compiler `design_mandate`
    /// bit" (the 2026-07-02 green-front-door plan, "Buckets"; deleted in
    /// `6ba5324748`, read it with `git show
    /// 6ba5324748^:docs/design-notes/2026-07-02-green-front-door-plan.md`),
    /// and its F4 item requires a mandate row's outcome to "remain NON-FAILED",
    /// root-caused in the hardened routing if it fails — never re-bucketed here.
    fn failed_unmodeled_call_mandate_result() -> VerificationResult {
        let kind = VcKind::Assertion {
            message: "[unsafe:unmodeled-call] call to `libc::memcpy` (unsafe fn) is not \
                      covered by Trust's model (fail-closed — no unsafe operation may \
                      silently pass)"
                .into(),
        };
        let transport = trust_types::TransportObligationResult {
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: None,
            claim_digest_sha256: None,
            kind: kind.transport_tag(),
            original_vc_snapshot: None,
            typed_kind: Some(Box::new(kind.clone())),
            description: kind.description(),
            location: Some(SourceSpan {
                file: "src/layernorm.rs".into(),
                line_start: 91,
                col_start: 9,
                line_end: 91,
                col_end: 34,
            }),
            outcome: trust_types::Outcome::Failed,
            solver: "ay-smtlib".into(),
            time_ms: 1,
            counterexample: Some("unmodeled call".into()),
            counterexample_model: None,
            reason: None,
            design_mandate: true,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            grade: None,
        };
        transport_to_verification_result("crate::layernorm::forward", &transport, None, None)
    }

    /// END-TO-END pin for a refuted row that carries the compiler's
    /// design-mandate bit: BOTH accounts must put it in `failed`.
    ///
    /// `the_canonical_projection_keeps_every_bucket_the_gate_assigned` pins the
    /// partition and the `counts_as_design_mandate` predicate. Neither assertion
    /// constrains `to_trust_report`, which is the side that actually drifted
    /// (MEASURED on trust-wp 2026-09-13: `total_failed 1113 != 1185`, exactly 72
    /// such rows). Reverting that projection to the raw `transport_design_mandate`
    /// bit would leave both of those assertions green while the canonical report
    /// again labelled the row a `DesignRequirement` — dropping a REFUTATION out of
    /// `total_failed`, which in the advisory lane turns a Fail (exit 1) into a
    /// ConditionalPass (exit 0) without proving anything. Pin the projection
    /// itself, on the real `[unsafe:unmodeled-call]` shape.
    ///
    /// G3-MANDATE-L1-ONLY-1: the `[unsafe:unmodeled-call]` specimen still carries
    /// the raw bit, but as an L0 modelling gap it is no longer a mandate at all;
    /// the same pin runs on an L1 `ProcessSemantics` twin that IS one.
    #[test]
    fn a_refuted_design_mandate_row_is_failed_in_both_accounts() {
        let specimen = failed_unmodeled_call_mandate_result();
        assert!(
            structured_transport_evidence(&specimen)
                .is_some_and(|evidence| evidence.design_mandate),
            "fixture must carry the compiler's design-mandate bit",
        );
        assert!(!transport_design_mandate(&specimen), "an L0 gap is never a mandate");

        let mut l1_twin = specimen.clone();
        let kind = VcKind::HardenedBoundary {
            category: HardenedVcCategory::ProcessSemantics,
            callee: "std::process::exit".into(),
            detail: "process semantics".into(),
        };
        let mut evidence = structured_transport_evidence(&l1_twin).expect("structured row");
        evidence.typed_kind = Some(Box::new(kind.clone()));
        crate::types::replace_structured_transport_evidence(&mut l1_twin, &evidence)
            .expect("replace structured evidence");
        l1_twin.kind = kind.transport_tag();
        l1_twin.message = kind.description();
        assert!(transport_design_mandate(&l1_twin), "the L1 twin carries a real mandate bit");

        for row in [specimen, l1_twin] {
            assert_refuted_mandate_bit_row_is_failed_in_both_accounts(row);
        }
    }

    fn assert_refuted_mandate_bit_row_is_failed_in_both_accounts(row: VerificationResult) {
        assert_eq!(row.outcome, VerificationOutcome::Failed, "and it must be REFUTED");

        // Account 1 — the exit-code gate's partition.
        let (counts, defects) =
            crate::pipeline::hardened::partition_outcome_counts(std::slice::from_ref(&row));
        assert_eq!(counts.failed, 1, "the gate counts a refuted mandate as a refutation");
        assert_eq!(counts.mandated, 0, "and never as a design mandate");
        assert!(defects.is_empty(), "a refuted mandate is not a transport defect: {defects:?}");

        // Account 2 — the canonical projection users see, under LIVE row
        // authority (without it the row could never be labelled a design
        // requirement, so the test would pass for the wrong reason).
        let report =
            with_live_transport_authority(report_with_results_and_diagnostics(vec![row], vec![]));
        assert_eq!(report.failed, 1, "the sealed internal partition agrees");
        assert_eq!(report.mandated, 0);

        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_failed, 1, "the refutation must stay in total_failed",);
        assert_eq!(
            canonical.summary.total_design_requirements, 0,
            "a refuted row is not a requirement the design owes",
        );
        assert!(
            canonical
                .functions
                .iter()
                .flat_map(|function| &function.obligations)
                .any(|obligation| matches!(&obligation.outcome, ObligationOutcome::Failed { .. })),
            "and it must render as a FAILURE, not a DesignRequirement: {:?}",
            canonical
                .functions
                .iter()
                .flat_map(|function| &function.obligations)
                .map(|obligation| &obligation.outcome)
                .collect::<Vec<_>>(),
        );

        // Account 3 — the seal's gate/canonical equality check, which is where a
        // disagreement between the two actually kills a run.
        assert_eq!(
            report.canonical_report_state_divergence(&canonical),
            None,
            "gate and projection must agree on a refuted mandate row",
        );
    }

    /// Trust (2026-10-02, diag-vs-report): the transport row of an absent-callee
    /// call through an OPEN, uncontracted generic dispatch, as the compiler
    /// published it before and after it stamped its Level-0 refutation onto the
    /// row (`trust_types::l0_refutation::reclassify_published_row`).
    fn open_dispatch_absent_callee_result(stamped: bool) -> VerificationResult {
        let kind = VcKind::Assertion {
            message: "[trust-absent-callee-assumption] call to absent callee \
                      `<T as core::clone::Clone>::clone` (body not in the lowered bundle) \
                      may panic"
                .into(),
        };
        let mut transport = trust_types::TransportObligationResult {
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: None,
            claim_digest_sha256: None,
            kind: kind.transport_tag(),
            original_vc_snapshot: None,
            typed_kind: Some(Box::new(kind.clone())),
            description: kind.description(),
            location: None,
            outcome: trust_types::Outcome::RuntimeChecked,
            solver: "trust-full-verifier".into(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: Some("native full verifier evidence status: Unsupported".into()),
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            grade: None,
        };
        if stamped {
            assert!(trust_types::l0_refutation::reclassify_published_row(
                &mut transport,
                trust_types::l0_refutation::L0RefutationClass::AdversarialOpenDispatch,
            ));
        }
        transport_to_verification_result("crate::Wrap::clone", &transport, None, None)
    }

    /// The compiler's Level-0 summary line said "1 failed" for this row while the
    /// row said `runtime_checked`, so the advisory gate (`--allow-l0-gaps`)
    /// conditional-passed what the compiler called a refutation. Once the row is
    /// stamped, every account says `failed`: the gate partition, the canonical
    /// report, and the decision in EVERY lane. The control half pins that the
    /// stamp can only make a decision stricter: strict and certify already exit
    /// nonzero on this run (the compiler aborts on the same refutation), and
    /// advisory moves from a conditional pass to a failure — never the reverse.
    #[test]
    fn a_compiler_l0_refutation_is_failed_in_every_account() {
        use crate::pipeline::hardened::{
            GateDecision, GateLane, evaluate_verification_gate, partition_outcome_counts,
        };

        let unstamped = open_dispatch_absent_callee_result(false);
        let stamped = open_dispatch_absent_callee_result(true);
        assert_eq!(stamped.outcome, VerificationOutcome::Failed);

        let (before, _) = partition_outcome_counts(std::slice::from_ref(&unstamped));
        let (after, defects) = partition_outcome_counts(std::slice::from_ref(&stamped));
        assert_eq!((before.failed, before.runtime_checked), (0, 1));
        assert_eq!((after.failed, after.runtime_checked), (1, 0));
        assert!(defects.is_empty(), "a stamped refutation is not a transport defect: {defects:?}");

        // Control: the compiler exits nonzero under strict/certify/memory-safe for
        // this refutation (measured on stage-1 b0b9258cc9, rc=1 each), so those
        // lanes FAIL before and after; advisory (compiler rc=0) tightens.
        for lane in [GateLane::Strict, GateLane::Certify, GateLane::MemorySafe] {
            assert_eq!(evaluate_verification_gate(lane, 1, before), GateDecision::Fail);
            assert_eq!(evaluate_verification_gate(lane, 1, after), GateDecision::Fail);
        }
        assert!(evaluate_verification_gate(GateLane::Advisory, 0, before).is_success());
        assert_eq!(evaluate_verification_gate(GateLane::Advisory, 0, after), GateDecision::Fail);
        // No lane may turn more permissive for any compiler exit.
        for lane in [GateLane::Advisory, GateLane::Strict, GateLane::Certify, GateLane::MemorySafe]
        {
            for exit in [0, 1] {
                let was = evaluate_verification_gate(lane, exit, before).is_success();
                let now = evaluate_verification_gate(lane, exit, after).is_success();
                assert!(was || !now, "{lane:?} exit={exit} became more permissive");
            }
        }

        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![stamped],
            vec![],
        ));
        assert_eq!(report.failed, 1);
        assert_eq!(report.runtime_checked, 0);
        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_failed, 1, "report.json must say failed too");
        assert_eq!(report.canonical_report_state_divergence(&canonical), None);
    }

    /// The same stamped row as [`open_dispatch_absent_callee_result`], but with the
    /// solver label the stamp wrote before 2026-10-03 (the verifier's bare
    /// `trust-full-verifier`), i.e. the row as it read when every reader called it
    /// `refuted`. The CONTROL for the l0-failure-basis relabel.
    fn open_dispatch_absent_callee_result_with_legacy_label() -> VerificationResult {
        let mut row = open_dispatch_absent_callee_result(true);
        assert!(trust_types::is_fail_closed_solver_label(&row.backend), "{}", row.backend);
        row.backend = "trust-full-verifier".into();
        row
    }

    /// Drop the only fields the relabel may change — the failure basis, its
    /// subset counts and the solver label — so the rest of a report can be
    /// compared byte for byte.
    fn without_basis_and_label(mut value: serde_json::Value) -> serde_json::Value {
        fn strip(value: &mut serde_json::Value) {
            match value {
                serde_json::Value::Object(map) => {
                    for key in ["basis", "failed_unproved", "total_failed_unproved", "solver"] {
                        map.remove(key);
                    }
                    map.values_mut().for_each(strip);
                }
                serde_json::Value::Array(items) => items.iter_mut().for_each(strip),
                _ => {}
            }
        }
        strip(&mut value);
        value
    }

    /// 2026-10-03 (l0-failure-basis): a compiler-stamped Level-0 refutation has no
    /// counterexample and no engine refuted it, so it reads "unproved, no
    /// counterexample; failed closed" on the terminal and `unproved_fail_closed` in
    /// report.json — not `refuted`. CONTROL: against the identical row under its
    /// pre-fix label, the gate partition, every lane's decision for every compiler
    /// exit, the canonical counts and verdict, and the whole report.json except the
    /// basis/label fields are byte-identical.
    #[test]
    fn a_compiler_l0_refutation_reads_unproved_and_moves_no_count() {
        use trust_types::FailureBasis;

        use crate::pipeline::hardened::{
            GateLane, evaluate_verification_gate, partition_outcome_counts,
        };

        let stamped = open_dispatch_absent_callee_result(true);
        let legacy = open_dispatch_absent_callee_result_with_legacy_label();
        assert_eq!(stamped.failure_basis(), Some(FailureBasis::UnprovedFailClosed));
        assert_eq!(legacy.failure_basis(), Some(FailureBasis::Refuted));
        assert!(stamped.backend.ends_with(":trust-full-verifier"), "{}", stamped.backend);
        assert!(is_full_verifier_result(&stamped), "the full-verifier recognizer still matches");
        assert_eq!(is_unsafe_memory_result(&stamped), is_unsafe_memory_result(&legacy));
        assert_eq!(
            unsafe_memory_result_has_forbidden_marker(&stamped),
            unsafe_memory_result_has_forbidden_marker(&legacy)
        );

        // Terminal: only the label changes.
        let line = terminal_result_line(&stamped);
        assert!(
            line.starts_with("  [FAILED: unproved, no counterexample; failed closed] "),
            "{line}"
        );
        assert!(terminal_result_line(&legacy).starts_with("  [FAILED] "));

        // Gate: identical partition and identical decision in every lane.
        let (after, after_defects) = partition_outcome_counts(std::slice::from_ref(&stamped));
        let (before, before_defects) = partition_outcome_counts(std::slice::from_ref(&legacy));
        assert_eq!(after, before, "the exit-code gate's partition must not move");
        assert_eq!(after_defects, before_defects);
        for lane in [GateLane::Advisory, GateLane::Strict, GateLane::Certify, GateLane::MemorySafe]
        {
            for exit in [0, 1, 101] {
                assert_eq!(
                    evaluate_verification_gate(lane, exit, after),
                    evaluate_verification_gate(lane, exit, before),
                    "{lane:?} exit={exit}"
                );
            }
        }
        assert_eq!(failed_unproved_rows(std::slice::from_ref(&stamped)), 1);
        assert_eq!(failed_unproved_rows(std::slice::from_ref(&legacy)), 0);

        // report.json: the basis says unproved; every count and the verdict match.
        let new_report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![stamped],
            vec![],
        ));
        let old_report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![legacy],
            vec![],
        ));
        assert_eq!(
            (new_report.failed, new_report.exit_code, new_report.success),
            (old_report.failed, old_report.exit_code, old_report.success)
        );
        let new_json = new_report.to_trust_report();
        let old_json = old_report.to_trust_report();
        assert_eq!(new_report.canonical_report_state_divergence(&new_json), None);
        assert_eq!(new_json.summary.total_failed, 1);
        assert_eq!(new_json.summary.total_failed_unproved, 1);
        assert_eq!(old_json.summary.total_failed_unproved, 0);
        assert_eq!(new_json.summary.verdict, old_json.summary.verdict);
        let obligation = &new_json.functions[0].obligations[0];
        assert!(obligation.outcome.is_unproved_fail_closed(), "{:?}", obligation.outcome);
        assert_eq!(
            without_basis_and_label(serde_json::to_value(&new_json).expect("report serializes")),
            without_basis_and_label(serde_json::to_value(&old_json).expect("report serializes")),
            "report.json may differ only in the basis and the solver label"
        );
    }

    /// A gate-`assumed` row must not read as a "declared contract panic" in
    /// report.json, and a timeout must never read as an assumption. On
    /// trust-vc-types (survey 2026-10-02) the 17 `assumption:expected-absent-callee`
    /// rows said "declared contract panic", and 17 genuine timeouts were then
    /// mistaken for the gate's 17 `assumed`.
    #[test]
    fn assumption_rows_say_assumed_and_timeouts_stay_unknown() {
        use crate::pipeline::hardened::partition_outcome_counts;

        let mut assumption = full_verifier_result(VerificationOutcome::Unknown);
        assumption.kind = "assumption:expected-absent-callee".into();
        assumption.backend = "trust-bridge".into();
        let timeout = full_verifier_result(VerificationOutcome::Timeout);

        let (counts, _) = partition_outcome_counts(&[assumption.clone(), timeout.clone()]);
        assert_eq!(counts.assumed, 1, "the assumption row is `assumed`");
        assert_eq!(counts.unknown, 1, "the timeout is a genuine unknown, never `assumed`");

        let canonical = report_with_results_and_diagnostics(vec![assumption, timeout], vec![])
            .to_trust_report();
        let outcomes: Vec<&ObligationOutcome> = canonical
            .functions
            .iter()
            .flat_map(|function| &function.obligations)
            .map(|obligation| &obligation.outcome)
            .collect();
        assert!(
            outcomes.iter().any(|outcome| matches!(
                outcome,
                ObligationOutcome::Unknown { reason }
                    if reason.contains("counts as `assumed`")
                        && !reason.contains("declared contract panic")
            )),
            "{outcomes:?}",
        );
        // The timeout reaches the canonical report as a timeout (or, through the
        // fail-closed static adapter, an unknown that says it timed out) — never
        // as conditional evidence.
        assert!(
            outcomes.iter().any(|outcome| match outcome {
                ObligationOutcome::Timeout { .. } => true,
                ObligationOutcome::Unknown { reason } =>
                    reason.contains("timed out") && !reason.contains("assumed"),
                _ => false,
            }),
            "{outcomes:?}",
        );
        assert_eq!(
            conditional_evidence_report_reason(true),
            "declared contract panic (conditional policy row; no proof credit)",
            "a real declared contract panic keeps its label",
        );
    }

    /// The gate and the canonical projection must count DESIGN MANDATES the same
    /// way. They did not: the projection read the compiler's `design_mandate` bit
    /// off any authorized row, while `partition_outcome_counts` counts a mandate
    /// only on an INCONCLUSIVE row (every other branch `continue`s first). A row
    /// carrying the bit and claiming PROVED therefore counted on one side only,
    /// and `mandated.checked_sub(authorized_mandated)` underflowed — refusing the
    /// seal of a clean run through a bare `return false`. MEASURED on trust-wp
    /// 2026-09-13: 116 authorized mandates against 78 partitioned.
    #[test]
    fn a_proved_row_carrying_the_mandate_bit_is_not_counted_as_a_mandate() {
        let mut mandated = full_verifier_result(VerificationOutcome::Unknown);
        mandated.kind = "hardened_process_semantics".into();
        mandated.raw_line =
            format!("targo-trust-structured-transport-evidence:{}", r#"{"design_mandate":true}"#,);
        assert!(
            transport_design_mandate(&mandated),
            "fixture must carry the compiler's design-mandate bit",
        );
        assert!(
            crate::pipeline::hardened::counts_as_design_mandate(&mandated),
            "an INCONCLUSIVE row with the bit is what the gate counts as a mandate",
        );

        // Same row, same bit, but it CLAIMS proof. The gate does not count it as a
        // mandate (it takes the `proved` bucket), so neither may the projection.
        let mut claims_proof = mandated.clone();
        claims_proof.outcome = VerificationOutcome::Proved;
        assert!(
            transport_design_mandate(&claims_proof),
            "the bit is still set — only the outcome differs",
        );
        assert!(
            !crate::pipeline::hardened::counts_as_design_mandate(&claims_proof),
            "a row claiming proof is counted as proved, never as a design mandate",
        );

        // And the partition agrees with itself: one mandate, not two.
        let (counts, _) = crate::pipeline::hardened::partition_outcome_counts(&[
            mandated.clone(),
            claims_proof.clone(),
        ]);
        assert_eq!(counts.mandated, 1);
        assert_eq!(counts.proved, 1);
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
            publication_boundary: None,
            zero_obligation_functions: Vec::new(),
            compiler_diagnostics: vec![CompilerDiagnostic {
                level: "note".into(),
                message: "native full verifier status: Proved; requested=1, proved=1, failed=0"
                    .into(),
            }],
            duration_ms: 11,
            config: ReportConfig {
                level: "L1".into(),
                budget_profile: crate::determinism_report::test_budget_profile(),
                enabled: true,
                hardened: false,
                trust_profile: None,
                project_requirements: None,
            },
            dep_assumptions: Vec::new(),
            gate: None,
            noted_stops: Vec::new(),
            coverage: None,
            coverage_dropped: Vec::new(),
            test_execution: None,
            cargo_proof_inventory: None,
            proof_artifact_root: None,
            live_transport_authority: None,
            test_harness_exclusions: Vec::new(),
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
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: None,
            claim_digest_sha256: None,
            kind: "postcond".into(),
            original_vc_snapshot: None,
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
            grade: None,
        };
        let result = transport_to_verification_result("crate::quantified", &transport, None, None);
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

    /// Trust (TINV step 10.7): a transport row's `assumes` disclosure reaches the canonical
    /// report row (and so report.json, NDJSON and every renderer) and the assumption
    /// ledger, whatever outcome the row ends with; a row without one carries none.
    #[test]
    fn transport_assumes_reach_the_report_row_and_the_ledger() {
        let premise = "assumes type_invariant(c::P)#2 `i <= len(b)` [certificate: test]";
        let row = |assumes: Vec<String>, function: &str| {
            let transport = trust_types::TransportObligationResult {
                assumes,
                gap_class: None,
                monitor: None,
                obligation_id: None,
                claim_digest_sha256: None,
                kind: "bounds".to_string(),
                original_vc_snapshot: None,
                typed_kind: None,
                description: "index out of bounds".to_string(),
                location: None,
                outcome: trust_types::Outcome::Proved,
                solver: "ay".to_string(),
                time_ms: 0,
                counterexample: None,
                counterexample_model: None,
                reason: None,
                design_mandate: false,
                native_trust_ir: None,
                proof_evidence: None,
                grade: None,
            };
            crate::types::transport_to_verification_result(function, &transport, None, None)
        };
        let report = report_with_results_and_diagnostics(
            vec![row(vec![premise.to_string()], "c::P::rest"), row(vec![], "c::other")],
            vec![],
        );
        let canonical = report.to_trust_report();
        let obligations: Vec<_> = canonical
            .functions
            .iter()
            .flat_map(|f| f.obligations.iter().map(move |o| (&f.function, o)))
            .collect();
        let premised: Vec<_> = obligations.iter().filter(|(_, o)| !o.assumes.is_empty()).collect();
        assert_eq!(premised.len(), 1, "{obligations:?}");
        assert!(premised[0].0.contains("rest"), "{:?}", premised[0].0);
        assert_eq!(premised[0].1.assumes, vec![premise.to_string()]);
        let ledger: Vec<_> = canonical
            .assumptions
            .iter()
            .filter(|entry| entry.tag == TYPE_INVARIANT_ASSUMPTION_TAG)
            .collect();
        assert_eq!(ledger.len(), 1, "{:?}", canonical.assumptions);
        assert_eq!(ledger[0].detail, premise);
        // The serialized report carries it; a report without premises does not.
        let json = serde_json::to_string(&canonical).expect("serializes");
        assert!(json.contains("\"assumes\":[\"assumes type_invariant(c::P)#2"), "{json}");
        let plain = report_with_results_and_diagnostics(vec![row(vec![], "c::other")], vec![])
            .to_trust_report();
        assert!(!serde_json::to_string(&plain).expect("serializes").contains("\"assumes\""));
    }

    /// Review fold-in: when the report's function grouping is NOT a one-to-one projection
    /// of the transport rows, `attach_transport_assumes` no longer drops the disclosure:
    /// it attaches by the unique obligation id, and reports a row it cannot place as a
    /// `type-invariant-unattached` ledger diagnostic naming the premise.
    #[test]
    fn a_grouping_mismatch_attaches_assumes_by_id_or_reports_them() {
        let premise = "assumes type_invariant(c::P)#2 `i <= len(b)` [certificate: test]";
        let row = |id: Option<&str>| {
            let transport = trust_types::TransportObligationResult {
                assumes: vec![premise.to_string()],
                gap_class: None,
                monitor: None,
                obligation_id: id.map(str::to_string),
                claim_digest_sha256: None,
                kind: "bounds".to_string(),
                original_vc_snapshot: None,
                typed_kind: None,
                description: "index out of bounds".to_string(),
                location: None,
                outcome: trust_types::Outcome::Proved,
                solver: "ay".to_string(),
                time_ms: 0,
                counterexample: None,
                counterexample_model: None,
                reason: None,
                design_mandate: false,
                native_trust_ir: None,
                proof_evidence: None,
                grade: None,
            };
            crate::types::transport_to_verification_result("c::P::rest", &transport, None, None)
        };
        // A report whose `rest` has TWO obligation rows for ONE transport row: misaligned.
        let mismatched = |results: &[VerificationResult], ids: [Option<&str>; 2]| {
            let mut report =
                report_with_results_and_diagnostics(results.to_vec(), vec![]).to_trust_report();
            let function = report
                .functions
                .iter_mut()
                .find(|f| f.function.contains("rest"))
                .expect("the rest function");
            let extra = function.obligations[0].clone();
            function.obligations.push(extra);
            for (o, id) in function.obligations.iter_mut().zip(ids) {
                o.assumes.clear();
                o.obligation_id = id.map(str::to_string);
            }
            report
        };
        // (a) A unique matching id: attached to exactly that row, no diagnostic.
        let results = [row(Some("vc:rest:0"))];
        let mut report = mismatched(&results, [Some("vc:rest:1"), Some("vc:rest:0")]);
        let unattached = attach_transport_assumes(&mut report, &results);
        assert!(unattached.is_empty(), "{unattached:?}");
        let rest = report.functions.iter().find(|f| f.function.contains("rest")).unwrap();
        assert!(rest.obligations[0].assumes.is_empty());
        assert_eq!(rest.obligations[1].assumes, vec![premise.to_string()]);
        // (b) No id, or an ambiguous one: nothing attached, one named diagnostic.
        for (id, ids) in [
            (None, [Some("vc:rest:0"), Some("vc:rest:1")]),
            (Some("vc:rest:0"), [Some("vc:rest:0"), Some("vc:rest:0")]),
        ] {
            let results = [row(id)];
            let mut report = mismatched(&results, ids);
            let unattached = attach_transport_assumes(&mut report, &results);
            assert_eq!(unattached.len(), 1, "{unattached:?}");
            assert_eq!(unattached[0].tag, TYPE_INVARIANT_UNATTACHED_TAG);
            assert!(unattached[0].detail.contains(premise), "{}", unattached[0].detail);
            assert_eq!(unattached[0].subject, "c::P::rest");
            let rest = report.functions.iter().find(|f| f.function.contains("rest")).unwrap();
            assert!(rest.obligations.iter().all(|o| o.assumes.is_empty()));
        }
        // Control: an aligned report attaches positionally and reports nothing.
        let results = [row(None)];
        let mut aligned =
            report_with_results_and_diagnostics(results.to_vec(), vec![]).to_trust_report();
        for f in &mut aligned.functions {
            for o in &mut f.obligations {
                o.assumes.clear();
            }
        }
        assert!(attach_transport_assumes(&mut aligned, &results).is_empty());
        assert!(
            aligned.functions.iter().flat_map(|f| &f.obligations).any(|o| !o.assumes.is_empty())
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
            publication_boundary: None,
            zero_obligation_functions: Vec::new(),
            compiler_diagnostics,
            duration_ms: 11,
            config: ReportConfig {
                level: "L1".into(),
                budget_profile: crate::determinism_report::test_budget_profile(),
                enabled: true,
                hardened: false,
                trust_profile: None,
                project_requirements: None,
            },
            dep_assumptions: Vec::new(),
            gate: None,
            noted_stops: Vec::new(),
            coverage: None,
            coverage_dropped: Vec::new(),
            test_execution: None,
            cargo_proof_inventory: None,
            proof_artifact_root: None,
            live_transport_authority: None,
            test_harness_exclusions: Vec::new(),
        }
    }

    /// Rebuild a run-level `VerificationReport` from real compiler transport
    /// lines the way `pipeline::run` does, so the final publication seal can be
    /// replayed offline against rows a real `trustc` actually emitted.
    ///
    /// The ONLY reason this exists is that the seal is the last gate before any
    /// verdict is printed: when it refuses, the run publishes nothing at all, so
    /// a refusal cannot be reproduced from a saved report — by then there is no
    /// report. This mirrors the production order exactly: transport rows ->
    /// `normalize_authenticated_results_for_publication` -> outcome partition ->
    /// gate -> live authority -> seal.
    /// A run whose obligations a REAL `trustc` produced must end in a published
    /// verdict, never in silence.
    ///
    /// The fixture is verbatim `TRUST_JSON:` transport captured from
    /// `build/host/stage1/bin/trustc` compiling `crates/trust-endian`, the crate
    /// whose strict gate reported "no Gate: line — the lane did not run
    /// (vacuous)" on 2026-09-15 while `targo trust check -p trust-endian` exited
    /// 2 having printed no `Summary:`, no `Gate:` and no coverage row.
    #[test]
    fn a_real_compiler_transport_capture_publishes_a_verdict() {
        let transport = include_str!("fixtures/trust_endian_transport_partial.jsonl");
        let functions =
            transport.lines().filter(|line| line.contains("\"type\":\"function_result\"")).count();
        let coverage = Some(trust_types::VerificationCoverage {
            eligible: functions,
            processed: functions,
            coverage_complete: true,
            excluded: 0,
        });
        let mut report = report_from_transport_lines(transport, coverage);

        let outcome = report.seal_publication_state();

        assert_eq!(
            outcome,
            Ok(()),
            "rows a real compiler produced must reach publication; refused precondition: {:?}",
            outcome.as_ref().err().map(SealRefusal::precondition)
        );
    }

    /// The `trust.obligations.v1` record of `report`'s rows (a real compiler's
    /// rows, through the production record writer) for package `trust-endian`,
    /// as a crate-mode run writes it.
    fn real_obligation_records(
        report: &VerificationReport,
    ) -> crate::obligations::ObligationRecords {
        let coverage = [trust_types::CoverageTransportSummary {
            crate_name: "trust_endian".to_string(),
            package_name: "trust-endian".to_string(),
            primary_package: true,
            verification_session: "session".to_string(),
            eligible: 1,
            processed: 1,
            function_identities: None,
            noted_stops: Vec::new(),
            degraded_anchors: 0,
            memory: trust_types::MemorySummary::default(),
        }];
        crate::obligations::ObligationRecords::of_rows(
            &report.results,
            &crate::obligations::FunctionInventory::of_rows(&report.results),
            crate::obligations::RunFacts {
                lane: "strict".to_string(),
                policy: "strict".to_string(),
                selection: "--lib".to_string(),
                targo_trust_commit: "0123456789abcdef0123456789abcdef01234567".to_string(),
                profile: "a".repeat(64),
                worker_threads: 0,
                outcome: trust_types::determinism::UnitOutcome::Measured,
                vector: "b".repeat(64),
                coverage_complete: true,
                degraded_anchors: 0,
            },
            crate::obligations::RunScope::default(),
            &crate::package_record::RunCoverage {
                rows: &coverage,
                missing: std::collections::BTreeSet::new(),
                publication_stops: &[],
                compile_errors: &[],
            },
        )
    }

    /// Live-edit-loop step 2 on a crate-mode run's real rows (the verbatim
    /// `trustc` capture of `crates/trust-endian`): the terminal report a check
    /// prints with the changed-only view. With no base the full per-row listing
    /// stays and the package's summary line follows it; once the caller has a
    /// base, the view replaces only the per-row listing (one line when nothing
    /// changed, the changed row plus one line after a verdict changes), and every
    /// other line of the report — header, `Summary:`, gate — is unchanged.
    /// The trust-endian capture predates the compiler's stable obligation ids
    /// (T9: `stable_ids`, `source_sha256`), so its rows carry no key and a
    /// record of them is could-not-run. Add, per envelope, what a current
    /// compiler adds: one id per row from the shared minter
    /// (`obligation_identity::local_ids` over each row's kind and span start)
    /// and the function's source digest. Every row field is the capture's own.
    fn keyed_transport(transport: &str) -> String {
        use trust_types::obligation_identity::{KeyedRow, function_source_digest, local_ids};
        let mut out = String::new();
        for line in transport.lines() {
            let Some(json) = line.trim().strip_prefix("TRUST_JSON:") else {
                out.push_str(line);
                out.push('\n');
                continue;
            };
            let mut value: serde_json::Value = serde_json::from_str(json).unwrap();
            if value["type"] == "function_result" {
                let rows: Vec<(String, String, String, (u32, u32))> = value["results"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|row| {
                        let location = &row["location"];
                        let at = |field: &str| {
                            u32::try_from(location[field].as_u64().unwrap_or(0)).unwrap()
                        };
                        (
                            row["kind"].as_str().unwrap().to_string(),
                            format!("span:{}:{}", at("line_start"), at("col_start")),
                            row["description"].as_str().unwrap_or_default().to_string(),
                            (at("line_start"), at("col_start")),
                        )
                    })
                    .collect();
                let keyed: Vec<KeyedRow<'_>> = rows
                    .iter()
                    .map(|(kind, anchor, discriminator, position)| KeyedRow {
                        kind,
                        anchor,
                        position: *position,
                        discriminator,
                    })
                    .collect();
                let ids = local_ids(&keyed).expect("distinct ids");
                value["stable_ids"] = serde_json::json!(ids);
                value["source_sha256"] =
                    serde_json::json!(function_source_digest(value["function"].as_str().unwrap()));
            }
            out.push_str(&format!("TRUST_JSON:{value}\n"));
        }
        out
    }

    /// The report of the keyed trust-endian capture and its records.
    fn endian_report() -> (VerificationReport, crate::obligations::ObligationRecords) {
        let transport =
            keyed_transport(include_str!("fixtures/trust_endian_transport_partial.jsonl"));
        let transport = transport.as_str();
        let functions =
            transport.lines().filter(|line| line.contains("\"type\":\"function_result\"")).count();
        let coverage = Some(trust_types::VerificationCoverage::from_counts(functions, functions));
        let report = report_from_transport_lines(transport, coverage);
        let records = real_obligation_records(&report);
        (report, records)
    }

    /// The listing lines of `report`'s rows the listing does not label a
    /// plain `PROVED`.
    fn not_plainly_proved_lines(report: &VerificationReport) -> Vec<String> {
        report
            .results
            .iter()
            .map(terminal_result_line_and_label)
            .filter(|(_, label)| !listing_label_is_plain_proof(label))
            .map(|(line, _)| line)
            .collect()
    }

    /// The strict gate scripts (`scripts/trust_*_strict_gate.sh`) run
    /// `targo trust check --all-rows -p <crate>` again and again in one target
    /// directory, from an aterm tab whose session names a caller, and grep the
    /// per-row listing. On that path the listing is printed on every run, base
    /// or not: the output those scripts read never depends on the session
    /// environment.
    #[test]
    fn a_gate_scripts_check_run_twice_in_one_session_still_prints_the_listing() {
        let mut args: Vec<String> =
            ["check", "--all-rows", "-p", "trust-endian"].map(str::to_string).to_vec();
        let request = crate::agent_delta::DeltaRequest::take_from(&mut args).unwrap();
        assert_eq!(args, ["check", "-p", "trust-endian"], "`--all-rows` is targo's, not Cargo's");
        let (report, records) = endian_report();
        let listing: Vec<String> = report.results.iter().map(terminal_result_line).collect();
        let target = tempfile::tempdir().unwrap();
        for run in 0..3 {
            let view =
                crate::agent_delta::publish_run(target.path(), &records, &request, Some("tab"));
            assert_eq!(view.packages[0].since.is_some(), run > 0, "run {run}");
            assert!(!view.replaces_listing());
            let lines = report.terminal_lines_with(Some(&view));
            assert!(
                listing.iter().all(|row| lines.contains(row)),
                "run {run} keeps every listing row"
            );
            assert_eq!(view.commit_pointers(), Vec::<String>::new(), "printed: the pointer moves");
        }
    }

    #[test]
    fn a_real_runs_terminal_report_shows_only_what_changed_since_the_callers_base() {
        let (report, records) = endian_report();
        let ndjson = records.package_ndjson("trust-endian").expect("a trust-endian record");
        let rows = crate::obligations::parse_package_ndjson(&ndjson).unwrap().obligations.len();
        assert!(rows >= 2, "{ndjson}");
        // The capture publishes its rows unproved, so each prints on every run.
        let open = not_plainly_proved_lines(&report);
        assert!(open.len() >= 2, "{ndjson}");
        let target = tempfile::tempdir().unwrap();
        let request = crate::agent_delta::DeltaRequest::default();
        let listing: Vec<String> = report.results.iter().map(terminal_result_line).collect();
        let without = report.terminal_lines();

        let first = crate::agent_delta::publish_run(target.path(), &records, &request, Some("me"));
        let lines = report.terminal_lines_with(Some(&first));
        assert_eq!(first.commit_pointers(), Vec::<String>::new(), "printed: the pointer moves");
        let summary = first.packages[0].summary_line();
        assert_eq!(
            summary,
            format!(
                "trust-endian  {rows} obligation(s)  (now {})",
                first.packages[0].now.clone().unwrap()
            )
        );
        let position = lines.iter().position(|line| *line == summary).expect("the summary line");
        assert!(
            listing.iter().all(|row| lines[..position].contains(row)),
            "no base keeps the listing"
        );
        assert_eq!(lines.len(), without.len() + 1);

        let rerun = crate::agent_delta::publish_run(target.path(), &records, &request, Some("me"));
        let lines = report.terminal_lines_with(Some(&rerun));
        assert_eq!(rerun.commit_pointers(), Vec::<String>::new());
        assert!(
            listing.iter().filter(|row| !open.contains(row)).all(|row| !lines.contains(row)),
            "a base drops the plainly proved rows from the listing"
        );
        let unchanged = format!(
            "trust-endian  0 of {rows} changed since {now}  (now {now})",
            now = first.packages[0].now.clone().unwrap()
        );
        assert_eq!(lines.iter().filter(|line| line.starts_with("trust-endian  ")).count(), 1);
        assert!(lines.contains(&unchanged), "{lines:#?}");
        // Nothing changed, yet every row that is not plainly proved prints
        // again, as the listing prints it, and the view adds no row of its own.
        assert!(open.iter().all(|row| lines.contains(row)), "{lines:#?}");
        assert!(!lines.iter().any(|line| line.starts_with("STILL ")), "{lines:#?}");
        assert_eq!(lines.len(), without.len() - listing.len() + open.len() + 1);
        let tail = |lines: &[String]| {
            lines.iter().skip_while(|l| !l.starts_with("Summary:")).cloned().collect::<Vec<_>>()
        };
        assert_eq!(tail(&lines), tail(&without), "the Summary: and gate lines are the run's own");

        // One row's verdict changed (the capture's rows are published
        // unproved, so the first is made refuted): that row, labelled as the
        // listing labels it, and one summary line; the listing keeps every row
        // still not plainly proved, the changed one included.
        let mut edited = report.clone();
        assert_ne!(edited.results[0].outcome, VerificationOutcome::Failed);
        edited.results[0].outcome = VerificationOutcome::Failed;
        let edited_records = real_obligation_records(&edited);
        let after =
            crate::agent_delta::publish_run(target.path(), &edited_records, &request, Some("me"));
        let view = after.lines();
        let label = listing_label(
            &edited.results[0].kind,
            VerificationOutcome::Failed,
            edited.results[0].failure_basis(),
        );
        assert_eq!(view.len(), 2, "{view:#?}");
        assert!(view[0].starts_with(&format!("NEW FAILED  [{label}]  ")), "{view:#?}");
        assert!(view[1].starts_with(&format!("trust-endian  1 of {rows} changed since ")));
        let lines = edited.terminal_lines_with(Some(&after));
        assert!(lines.contains(&terminal_result_line(&edited.results[0])), "{lines:#?}");
        assert!(not_plainly_proved_lines(&edited).iter().all(|row| lines.contains(row)));

        // Another caller on the same target directory has no base.
        let other =
            crate::agent_delta::publish_run(target.path(), &records, &request, Some("other"));
        assert!(!other.replaces_listing());
    }

    /// Rows no view row stands for — a row with no stable key (every
    /// targo-synthesised `transport:*` row, and a compiler row whose key was
    /// refused) — still print, as the listing prints them, on a rerun under
    /// one caller whose view replaces the listing.
    #[test]
    fn a_rerun_under_one_caller_prints_every_row_with_no_key_that_is_not_proved() {
        let (mut report, _) = endian_report();
        let raw = include_str!("fixtures/trust_endian_transport_partial.jsonl");
        let functions =
            raw.lines().filter(|line| line.contains("\"type\":\"function_result\"")).count();
        let unkeyed = report_from_transport_lines(
            raw,
            Some(trust_types::VerificationCoverage::from_counts(functions, functions)),
        );
        let keyless: Vec<VerificationResult> = unkeyed
            .results
            .iter()
            .filter(|row| row.outcome != VerificationOutcome::Proved)
            .take(2)
            .cloned()
            .collect();
        assert_eq!(keyless.len(), 2, "the unkeyed capture has rows that are not proved");
        let mut transport = keyless[0].clone();
        transport.kind = "transport:missing_function_result".to_string();
        transport.message = "targo synthesised this row; it has no stable key".to_string();
        transport.outcome = VerificationOutcome::Unknown;
        report.results.extend(keyless);
        report.results.push(transport);
        let records = real_obligation_records(&report);
        let keyed_rows = {
            let ndjson = records.package_ndjson("trust-endian").expect("a trust-endian record");
            crate::obligations::parse_package_ndjson(&ndjson).unwrap().obligations.len()
        };
        assert!(keyed_rows + 3 <= report.results.len(), "three rows are in no record");
        let open = not_plainly_proved_lines(&report);
        let target = tempfile::tempdir().unwrap();
        let request = crate::agent_delta::DeltaRequest::default();
        for run in 0..2 {
            let view =
                crate::agent_delta::publish_run(target.path(), &records, &request, Some("tab"));
            assert_eq!(view.replaces_listing(), run > 0, "run {run}");
            let lines = report.terminal_lines_with(Some(&view));
            for row in &open {
                assert!(lines.contains(row), "run {run} prints {row}: {lines:#?}");
            }
            assert!(
                lines.iter().any(|line| line.starts_with("  [UNKNOWN] [transport:")),
                "run {run}: {lines:#?}"
            );
            assert_eq!(view.commit_pointers(), Vec::<String>::new());
        }
    }

    /// A run with no rows says so whether or not its view narrows the listing:
    /// the narrowed listing drops plainly proved rows only, never the empty
    /// run's line.
    #[test]
    fn an_empty_run_says_so_when_its_view_narrows_the_listing() {
        let (mut report, _) = endian_report();
        report.results.clear();
        let records = real_obligation_records(&report);
        let target = tempfile::tempdir().unwrap();
        let request = crate::agent_delta::DeltaRequest::default();
        for run in 0..2 {
            let view =
                crate::agent_delta::publish_run(target.path(), &records, &request, Some("tab"));
            assert_eq!(view.replaces_listing(), run > 0, "run {run}: {view:?}");
            let lines = report.terminal_lines_with(Some(&view));
            assert!(
                lines.iter().any(|line| line == "  No verification obligations found."),
                "run {run}: {lines:#?}"
            );
            assert_eq!(view.commit_pointers(), Vec::<String>::new());
        }
    }

    /// A crate-mode check moves the caller's pointer only once its report
    /// printed the view (`pipeline::run::render_report_for_run`). A run whose
    /// report is not printed (its report artifacts cannot be written, or it
    /// has no valid publication seal) leaves the base at the last token the
    /// caller was shown, so the next run still shows what changed since then.
    #[test]
    fn a_run_whose_report_is_not_printed_leaves_the_callers_base_where_it_was() {
        use crate::pipeline::run::{ReportRendering, render_report_for_run};
        let (mut report, records) = endian_report();
        report.seal_publication_state().unwrap();
        let target = tempfile::tempdir().unwrap();
        let request = crate::agent_delta::DeltaRequest::default();
        let render = |report: &VerificationReport,
                      view: &crate::agent_delta::DeltaView,
                      report_dir: Option<&str>| {
            render_report_for_run(
                report,
                ReportRendering::Stdout,
                OutputFormat::Terminal,
                report_dir,
                None,
                false,
                CompilerResourceReports::default(),
                Some(view),
                &mut None,
            )
        };
        let first = crate::agent_delta::publish_run(target.path(), &records, &request, Some("me"));
        render(&report, &first, None).expect("the report and its view are printed");
        let shown = first.packages[0].now.clone().unwrap();

        // One row refuted since.
        let mut edited = report.clone();
        edited.results[0].outcome = VerificationOutcome::Failed;
        let edited_records = real_obligation_records(&edited);
        let blocked = target.path().join("blocked");
        fs::write(&blocked, b"a file where the report directory goes").unwrap();
        for (why, report, report_dir) in [
            ("report artifacts not written", &report, blocked.to_str()),
            ("no valid publication seal", &edited, None),
        ] {
            let view = crate::agent_delta::publish_run(
                target.path(),
                &edited_records,
                &request,
                Some("me"),
            );
            assert_eq!(
                view.packages[0].since.as_ref().map(|(base, _)| base),
                Some(&shown),
                "{why}"
            );
            assert_ne!(view.packages[0].now.as_ref(), Some(&shown), "{why}: a new token");
            assert!(render(report, &view, report_dir).is_err(), "{why}: nothing printed");
        }

        // The base is still the token the caller saw, so the refuted row is
        // still a change.
        let next =
            crate::agent_delta::publish_run(target.path(), &edited_records, &request, Some("me"));
        assert_eq!(next.packages[0].since.as_ref().map(|(base, _)| base), Some(&shown));
        assert!(next.lines().iter().any(|line| line.starts_with("NEW FAILED  ")), "{next:#?}");
    }

    #[test]
    fn resealing_changed_test_execution_rebuilds_only_the_canonical_state_cache() {
        let transport = include_str!("fixtures/trust_endian_transport_partial.jsonl");
        let functions =
            transport.lines().filter(|line| line.contains("\"type\":\"function_result\"")).count();
        let mut report = report_from_transport_lines(
            transport,
            Some(trust_types::VerificationCoverage::from_counts(functions, functions)),
        );
        report.seal_publication_state().unwrap();
        let authority = report.live_transport_authority.as_ref().unwrap();
        let rows_before = authority.row_receipts.clone();
        assert!(!rows_before.is_empty(), "control retains real compiler rows");
        let complete_before = authority.complete_report_receipt;
        let canonical_before = authority.canonical_report_receipt;
        report.seal_publication_state().unwrap();
        let authority = report.live_transport_authority.as_ref().unwrap();
        assert_eq!(authority.complete_report_receipt, complete_before);
        assert_eq!(authority.canonical_report_receipt, canonical_before);

        report.success = false;
        report.exit_code = 101;
        let gate = report.gate.as_mut().unwrap();
        gate.decision = "fail".into();
        gate.exit_code = 101;
        gate.test_execution = Some(CertifiedTestExecutionReport {
            schema: trust_types::CERTIFIED_TEST_EXECUTION_SCHEMA_VERSION.into(),
            completion_scope: CertifiedTestExecutionCompletionScope::TopLevelCargoChildExitOnlyV1,
            requested: true,
            scope: trust_types::CERTIFIED_TEST_EXECUTION_SCOPE.into(),
            compile_only: false,
            phase_a_status: 0,
            phase_a_success: true,
            phase_b_state: CertifiedTestExecutionPhaseState::CargoInvocationExited,
            blocker: None,
            phase_b_exit: Some(101),
            authorized_executables: Vec::new(),
            authorized_inventory_sha256: None,
            target_directory: None,
        });
        report.test_execution = gate.test_execution.clone();
        report.seal_publication_state().unwrap();
        let authority = report.live_transport_authority.as_ref().unwrap();
        assert_eq!(
            authority.row_receipts, rows_before,
            "test outcomes cannot mint new row authority"
        );
        assert_ne!(authority.complete_report_receipt, complete_before);
        assert_ne!(authority.canonical_report_receipt, canonical_before);
        let gate =
            authority.sealed_canonical_report.as_ref().unwrap().verification_gate.as_ref().unwrap();
        assert_eq!(gate.exit_code, 101);
        assert_eq!(gate.test_execution.as_ref().unwrap().phase_b_exit, Some(101));
    }

    /// A crate whose only function raises no obligation PASSES the strict gate.
    ///
    /// The fixture is verbatim `TRUST_JSON:` transport from the installed
    /// `trustc 450403669` compiling a zero-dependency crate whose whole source
    /// is `pub fn one() -> u8 { 1 }`. Its envelope states the unit's
    /// `runtime_checks` (f888a642ae), which `transport_to_verification_result`
    /// binds to the `no_obligations` row as a structured payload. The coverage row's
    /// `memory` summary is the one the stage 1 of the T3 L4 merge `fd4cee44ece` publishes for
    /// the same source (captured 2026-10-21; the rest of the line is the original). The inventory
    /// matcher demanded NO payload, so the row missed the inventory shape, was
    /// relabelled `Unknown` "without an exact canonical claim digest", and
    /// `targo trust build` printed `Gate: INCONCLUSIVE [strict lane, exit 1]`
    /// (measured 2026-09-25) where the 321aaeda7 seal printed `Result: PASS`.
    #[test]
    fn a_zero_obligation_crate_stating_its_check_env_passes_the_strict_gate() {
        let transport = include_str!("fixtures/zero_obligation_fn_transport.jsonl");
        assert!(
            transport.contains("\"runtime_checks\":{\"overflow_checks\":true,\"ub_checks\":true}"),
            "control: the capture states the unit's runtime-check environment"
        );
        let coverage = Some(trust_types::VerificationCoverage {
            eligible: 1,
            processed: 1,
            coverage_complete: true,
            excluded: 0,
        });
        let mut report = report_from_transport_lines(transport, coverage);

        assert_eq!(report.zero_obligation_functions, ["one::one"]);
        assert!(report.results.is_empty(), "inventory is not an obligation: {:?}", report.results);
        assert_eq!((report.total, report.unknown), (0, 0));
        let boundary = report.publication_boundary.clone().expect("publication boundary");
        assert_eq!(boundary.inventory_elided, 1);
        assert_eq!(boundary.withheld(), 0, "nothing was withheld: {boundary:?}");
        let gate = report.gate.as_ref().expect("gate");
        assert_eq!((gate.decision.as_str(), gate.exit_code), ("pass", 0));
        assert_eq!(report.seal_publication_state(), Ok(()));
    }

    /// The same real capture, replayed WITH the captured proof-artifact root
    /// that production always supplies.
    #[test]
    fn a_real_compiler_transport_capture_publishes_a_verdict_with_an_artifact_root() {
        let transport = include_str!("fixtures/trust_endian_transport_partial.jsonl");
        let functions =
            transport.lines().filter(|line| line.contains("\"type\":\"function_result\"")).count();
        let coverage = Some(trust_types::VerificationCoverage {
            eligible: functions,
            processed: functions,
            coverage_complete: true,
            excluded: 0,
        });
        let artifact_root = tempfile::tempdir().expect("artifact root");
        let mut report = report_from_transport_lines_with_artifact_root(
            transport,
            coverage,
            Some(artifact_root.path()),
        );

        let outcome = report.seal_publication_state();

        assert_eq!(
            outcome,
            Ok(()),
            "rows a real compiler produced must reach publication; refused precondition: {:?}",
            outcome.as_ref().err().map(SealRefusal::precondition)
        );
    }

    /// A run whose final seal REFUSES must still publish a verdict: the rows
    /// that were established are published, anything claiming proof is graded
    /// UNKNOWN, the coverage row survives, a real `Gate:` line is printed, and
    /// the exit is nonzero — never silence.
    ///
    /// Pinned because the silent path let `scripts/trust_endian_strict_gate.sh`
    /// read a bare nonzero exit as "the strict lane REFUTED a byte-order swap"
    /// (line 370) while its own `gate_line()` found no `Gate:` line at all
    /// (line 106). A no-verdict run that reads as a verdict is the dangerous
    /// direction, so this asserts the published verdict claims NOTHING.
    #[test]
    fn a_refused_seal_publishes_a_fail_closed_verdict_instead_of_nothing() {
        let transport = include_str!("fixtures/trust_endian_transport_partial.jsonl");
        let functions =
            transport.lines().filter(|line| line.contains("\"type\":\"function_result\"")).count();
        let coverage = Some(trust_types::VerificationCoverage {
            eligible: functions,
            processed: functions,
            coverage_complete: true,
            excluded: 0,
        });
        let mut report = report_from_transport_lines(transport, coverage);
        assert_eq!(report.seal_publication_state(), Ok(()), "control: this capture seals");
        assert!(report.total > 0, "control: the capture carries rows to publish");

        // A row that CLAIMS proof the seal cannot vouch for — the shape a
        // refused proof certificate leaves behind. The run must publish it as
        // unknown rather than publish nothing at all.
        report.results[0].outcome = VerificationOutcome::Proved;
        report.proved += 1;
        report.unknown = report.unknown.saturating_sub(1);

        let refusal = report
            .seal_publication_state()
            .expect_err("a row the seal cannot vouch for must refuse to seal");

        report
            .grade_every_row_unproved_and_reseal(&refusal, 2)
            .expect("a refused seal must still publish a fail-closed verdict");

        let canonical = report.to_trust_report();
        let gate = canonical
            .verification_gate
            .as_ref()
            .expect("a published run must carry a verification gate");
        assert_eq!(gate.decision, "inconclusive", "a refused seal can never publish a pass");
        assert_eq!(gate.exit_code, 2, "the published gate must record the nonzero exit");
        assert_eq!(
            canonical.summary.total_proved, 0,
            "no obligation may be published as proved after a refused seal"
        );
        assert_eq!(gate.counts.total, report.total, "the whole row inventory is still published");
        assert!(gate.coverage.is_some(), "the coverage row must survive the repair");
        assert!(
            report.results.iter().all(|result| !result.outcome.is_proved()),
            "every row must be graded unproved"
        );
        assert!(
            report.results[0]
                .reason
                .as_deref()
                .is_some_and(|reason| reason.contains("publication seal refused")),
            "the demoted row must carry the refusal verbatim, not a bare unknown"
        );

        let rendered = trust_report::format_json_summary(&canonical);
        // Show what the run now publishes where a reader can see it: the whole
        // point of the fix is that this text exists at all, so the before/after
        // is readable in test output instead of inferred from assertions.
        eprintln!("--- terminal output published after a REFUSED seal ---");
        for line in report.terminal_lines() {
            eprintln!("{line}");
        }
        eprintln!("--- canonical summary ---");
        eprintln!("{rendered}");
        assert!(
            rendered.contains("Gate: INCONCLUSIVE"),
            "the run must print a real Gate line; rendered: {rendered}"
        );
    }

    /// Replay the seal over the EXACT authenticated row vector a failing
    /// production run persisted (`<target-dir>/trust-cache/verification.json`,
    /// written by `pipeline::run::persist_verification_snapshot`).
    ///
    /// This is the highest-fidelity offline input available: cargo-unit-
    /// qualified row identities, the real hardened profile, and the real
    /// evidence — the same vector the run held when it refused to seal and
    /// exited 2 having published nothing.
    ///
    /// Two deliberate edits to the capture, both structural only: it is trimmed
    /// to the four smallest functions (the whole 114-row capture is 2 MB, and
    /// the seal is row-count agnostic), and the capturing machine's absolute
    /// path is rewritten to `/workspace` so no developer home directory is
    /// checked in. Neither touches an outcome, a digest, or an evidence field.
    #[test]
    fn a_persisted_production_row_vector_publishes_a_verdict() {
        let authenticated_compiler_results: Vec<VerificationResult> =
            serde_json::from_str(include_str!("fixtures/trust_endian_authenticated_rows.json"))
                .expect("persisted production row vector should deserialize");
        let report_subject = authenticated_compiler_results[0]
            .function
            .rsplit_once("::trust_endian::")
            .map(|(subject, _)| subject.to_string())
            .expect("persisted rows carry a cargo-target qualified identity");

        let covered_functions = authenticated_compiler_results
            .iter()
            .map(|result| result.function.as_str())
            .collect::<std::collections::BTreeSet<_>>()
            .len();
        let zero_obligation_functions =
            crate::types::authenticated_zero_obligation_inventory(&authenticated_compiler_results);
        let mut results = authenticated_compiler_results.clone();
        let publication_boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut results, None);
        let (counts, _defects) = crate::pipeline::hardened::partition_outcome_counts(&results);

        let mut report = VerificationReport {
            report_subject: report_subject.clone(),
            success: counts.failed == 0 && counts.unknown == 0,
            exit_code: 0,
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
            publication_boundary: Some(publication_boundary),
            zero_obligation_functions,
            compiler_diagnostics: Vec::new(),
            duration_ms: 23,
            config: ReportConfig {
                level: "L2".into(),
                budget_profile: crate::determinism_report::test_budget_profile(),
                enabled: true,
                // The failing run reported `hardened profile `unix_hardened`
                // enabled`, and 48 of its 114 rows are hardened panic
                // boundaries. A replay with `hardened: false` would skip the
                // hardened proof-evidence gate production actually ran.
                hardened: true,
                trust_profile: Some("unix_hardened".to_string()),
                project_requirements: None,
            },
            dep_assumptions: Vec::new(),
            gate: None,
            noted_stops: Vec::new(),
            coverage: Some(trust_types::VerificationCoverage {
                // Derived from the fixture rather than hard-coded, so trimming
                // the capture cannot silently desynchronise the coverage row
                // from the rows it is supposed to account for.
                eligible: covered_functions,
                processed: covered_functions,
                coverage_complete: true,
                excluded: 0,
            }),
            coverage_dropped: Vec::new(),
            test_execution: None,
            cargo_proof_inventory: None,
            proof_artifact_root: None,
            live_transport_authority: None,
            test_harness_exclusions: Vec::new(),
        };
        report.live_transport_authority = LiveTransportAuthority::capture_authenticated_projection(
            &report.report_subject,
            "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
            authenticated_compiler_results,
            &report.results,
            None,
            crate::test_target_panics::TestTargetPanicPolicy::Strict,
        );
        assert!(
            report.live_transport_authority.is_some(),
            "persisted production rows must mint the live row authority"
        );

        // Mirror `run_compiler`'s order: the hardened proof-evidence gate can
        // flip success BEFORE the gate object is built and the seal runs.
        let hardened_gate_failure = report.hardened_proof_gate_failure();
        if hardened_gate_failure.is_some() {
            report.success = false;
        }
        let decision = if hardened_gate_failure.is_some() {
            "fail"
        } else if report.success {
            "pass"
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
                excluded: 0,
            },
            conditional_on_assumption_rows: counts.assumed > 0,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: counts.runtime_checked > 0,
            conditional_on_unknown_rows: false,
            conditional_on_visitation_entries: false,
            coverage: report.coverage,
            test_execution: None,
            exclusions: Vec::new(),
            determinism: None,
            failure_sites: None,
            project_requirements: None,
        });

        let outcome = report.seal_publication_state();

        assert_eq!(
            outcome,
            Ok(()),
            "a persisted production run must publish a verdict; hardened gate failure: {:?}; refused precondition: {:?}",
            hardened_gate_failure,
            outcome.as_ref().err().map(SealRefusal::precondition)
        );
    }

    fn report_from_transport_lines(
        transport: &str,
        coverage: Option<trust_types::VerificationCoverage>,
    ) -> VerificationReport {
        report_from_transport_lines_with_artifact_root(transport, coverage, None)
    }

    /// The same replay, with the captured proof-artifact root production always
    /// supplies. `run_compiler` sets `proof_artifact_root` to
    /// `Some(verification_session.artifact_root())` on EVERY run, so the seal
    /// always takes the `inline_authenticated_rows` branch that a `None` replay
    /// skips entirely.
    fn report_from_transport_lines_with_artifact_root(
        transport: &str,
        coverage: Option<trust_types::VerificationCoverage>,
        artifact_root: Option<&Path>,
    ) -> VerificationReport {
        let mut authenticated_compiler_results = Vec::new();
        let mut session = String::new();
        for line in transport.lines() {
            let Some(message) = trust_types::parse_transport_line(line) else {
                continue;
            };
            if let trust_types::TransportMessage::FunctionResult(func_result) = message {
                if session.is_empty() {
                    session = func_result.verification_session.clone();
                }
                let identities = crate::types::envelope_identities(&func_result);
                for (row, identity) in func_result.results.iter().zip(identities) {
                    // The envelope's check environment, exactly as
                    // `pipeline/transport.rs` passes it. Replaying with `None`
                    // hid that every row of a compiler stating the environment
                    // carries a structured payload, which is how a
                    // zero-obligation crate graded INCONCLUSIVE unseen.
                    authenticated_compiler_results.push(transport_to_verification_result(
                        &func_result.function,
                        row,
                        func_result.runtime_checks,
                        identity,
                    ));
                }
            }
        }
        assert!(
            !authenticated_compiler_results.is_empty(),
            "transport fixture must carry at least one obligation row"
        );

        let zero_obligation_functions =
            crate::types::authenticated_zero_obligation_inventory(&authenticated_compiler_results);
        let mut results = authenticated_compiler_results.clone();
        let publication_boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut results, None);
        let (counts, _defects) = crate::pipeline::hardened::partition_outcome_counts(&results);
        let success = counts.failed == 0 && counts.unknown == 0;
        let exit_code = i32::from(!success);

        let mut report = VerificationReport {
            report_subject: "trust-endian".to_string(),
            success,
            exit_code,
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
            publication_boundary: Some(publication_boundary),
            zero_obligation_functions: zero_obligation_functions.clone(),
            compiler_diagnostics: Vec::new(),
            duration_ms: 17,
            config: ReportConfig {
                level: "L2".into(),
                budget_profile: crate::determinism_report::test_budget_profile(),
                enabled: true,
                hardened: false,
                trust_profile: None,
                project_requirements: None,
            },
            dep_assumptions: Vec::new(),
            gate: None,
            noted_stops: Vec::new(),
            coverage,
            coverage_dropped: Vec::new(),
            test_execution: None,
            cargo_proof_inventory: None,
            proof_artifact_root: artifact_root.map(Path::to_path_buf),
            live_transport_authority: None,
            test_harness_exclusions: Vec::new(),
        };
        report.gate = Some(trust_types::VerificationGateReport {
            lane: "strict".into(),
            verification_level: Some(report.config.level.clone()),
            decision: if success { "pass" } else { "inconclusive" }.into(),
            exit_code: if success { 0 } else { 1 },
            counts: trust_types::VerificationGateCounts {
                total: counts.total,
                proved: counts.proved,
                failed: counts.failed,
                unknown: counts.unknown,
                runtime_checked: counts.runtime_checked,
                assumed: counts.assumed,
                mandated: counts.mandated,
                contract_panics: counts.contract_panics,
                excluded: 0,
            },
            conditional_on_assumption_rows: counts.assumed > 0,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: counts.runtime_checked > 0,
            conditional_on_unknown_rows: false,
            conditional_on_visitation_entries: false,
            coverage: report.coverage,
            test_execution: None,
            exclusions: Vec::new(),
            determinism: None,
            failure_sites: None,
            project_requirements: None,
        });
        report.live_transport_authority = LiveTransportAuthority::capture_authenticated_projection(
            &report.report_subject,
            &session,
            authenticated_compiler_results,
            &report.results,
            artifact_root,
            crate::test_target_panics::TestTargetPanicPolicy::Strict,
        );
        assert!(
            report.live_transport_authority.is_some(),
            "replayed transport must mint the same live row authority production mints"
        );
        report
    }

    fn with_live_transport_authority(mut report: VerificationReport) -> VerificationReport {
        let authenticated_compiler_results = report.results.clone();
        report.zero_obligation_functions =
            crate::types::authenticated_zero_obligation_inventory(&authenticated_compiler_results);
        // Trust (#220): this helper is the fixtures' stand-in for the real
        // publication step, so it records the boundary exactly as `run_compiler`
        // does — otherwise a terminal-rendering test would exercise a code path
        // production never takes.
        report.publication_boundary =
            Some(crate::types::normalize_authenticated_results_for_publication(
                &mut report.results,
                report.proof_artifact_root.as_deref(),
            ));
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
                excluded: 0,
            },
            conditional_on_assumption_rows: counts.assumed > 0,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: counts.runtime_checked > 0,
            conditional_on_unknown_rows: false,
            conditional_on_visitation_entries: false,
            coverage: report.coverage,
            test_execution: None,
            exclusions: Vec::new(),
            determinism: None,
            failure_sites: None,
            project_requirements: None,
        });
        report.live_transport_authority = LiveTransportAuthority::capture_authenticated_projection(
            &report.report_subject,
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
            authenticated_compiler_results,
            &report.results,
            report.proof_artifact_root.as_deref(),
            crate::test_target_panics::TestTargetPanicPolicy::Strict,
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
        let _: trust_types::JsonProofReport = serde_json::from_slice(
            &fs::read(output_dir.path().join("report.json")).expect("read report.json"),
        )
        .expect("persisted report.json should deserialize");
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
        let loaded = crate::saved_report::load_report(&output.path().join("report.json"))
            .expect("rooted report reload should retain diagnostic evidence");
        assert_eq!(loaded.sanitization.downgraded_proved, 1);
        assert_eq!(loaded.sanitization.evidence_defects, 1);
        assert_eq!(loaded.report.summary.total_proved, 0);
        assert_eq!(loaded.report.summary.total_unknown, 1);
        assert_eq!(loaded.report.summary.verdict, trust_types::CrateVerdict::Inconclusive);
    }

    /// The seal's rule is "no AMBIENT paths", not "no paths". A
    /// `<store>/sha256/<digest>` path is the one shape whose only variable
    /// component is the digest the seal already binds, so permitting it adds no
    /// authority — and refusing it is what forced every artifact inline and
    /// made ay's report exceed 4 GiB. A store path naming a DIFFERENT digest is
    /// still ambient and must still be refused.
    #[test]
    fn the_seal_permits_a_digest_derived_store_path_and_refuses_any_other() {
        let source = tempfile::tempdir().expect("source root");
        let (canonical, digest) = path_backed_canonical_report(source.path());
        assert!(
            !report_contains_ambient_path_materializations(&canonical),
            "a canonical content-addressed store path is not ambient"
        );

        // Repoint the same artifact at a well-formed store path for a DIFFERENT
        // digest: the shape is right, but it no longer names what the seal binds.
        let mut tampered = canonical.clone();
        let other = "0".repeat(64);
        let mut repointed = false;
        for function in &mut tampered.functions {
            for obligation in &mut function.obligations {
                let Some(evidence) = obligation.transport_evidence.as_mut() else { continue };
                let groups = evidence
                    .native_trust_ir
                    .as_mut()
                    .map(|native| &mut native.artifacts)
                    .into_iter()
                    .chain(evidence.proof_evidence.as_mut().map(|proof| &mut proof.artifacts));
                for artifacts in groups {
                    for artifact in artifacts.iter_mut() {
                        let Some(materialization) = artifact.materialization.as_mut() else {
                            continue;
                        };
                        if materialization.materialized_path.is_some() {
                            materialization.materialized_path = Some(format!(
                                "{}/sha256/{other}",
                                trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY
                            ));
                            repointed = true;
                        }
                    }
                }
            }
        }
        assert!(repointed, "fixture must contain a path-backed artifact to repoint");
        assert!(
            report_contains_ambient_path_materializations(&tampered),
            "a store path whose digest disagrees with the declared digest is ambient and must be refused"
        );
        let _ = digest;
    }

    #[test]
    fn path_backed_stdout_requires_authority_and_reinlines_exact_bytes() {
        let source = tempfile::tempdir().expect("source root");
        let (report, _digest) = sealed_path_backed_native_report(source.path());
        assert!(report.proof_artifact_root.is_none(), "seal must consume mutable path authority");
        let canonical_before_removal = report.to_trust_report();
        // Small artifacts are still inlined, so nothing path-backed survives here.
        assert!(!report_contains_ambient_path_materializations(&canonical_before_removal));

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
    fn native_admission_is_bound_to_report_and_retires_with_bundle() {
        let report = report_with_result(result_with_location(None), VerificationOutcome::Proved)
            .to_trust_report();
        let output = tempfile::tempdir().unwrap();
        let resources = crate::compiler_admission::Report::new(
            &BTreeSet::new(),
            &BTreeSet::new(),
            vec![],
            vec![],
        );
        write_report_artifacts_from_root_with_compiler_resources(
            &report,
            output.path(),
            "<html>resource</html>",
            None,
            None,
            None,
            CompilerResourceReports { admission: Some(&resources), ..Default::default() },
        )
        .unwrap();
        let bytes = fs::read(output.path().join("report.json")).unwrap();
        let sidecar: serde_json::Value = serde_json::from_slice(
            &fs::read(output.path().join(crate::compiler_admission::FILE_NAME)).unwrap(),
        )
        .unwrap();
        assert_eq!(
            sidecar["proof_report_hash"],
            format!("sha256:{}", trust_types::digest::stable_sha256_hex(&bytes))
        );
        assert_eq!(sidecar["availability"], "incomplete");
        write_report_artifacts(&report, output.path(), "<html>no resource producer</html>")
            .unwrap();
        assert!(!output.path().join(crate::compiler_admission::FILE_NAME).exists());
    }

    #[test]
    fn interrupted_admission_install_restores_previous_report_pair() {
        let output = tempfile::tempdir().unwrap();
        fs::write(output.path().join("report.json"), b"old report").unwrap();
        fs::write(output.path().join(crate::compiler_admission::FILE_NAME), b"old admission")
            .unwrap();
        let staged = tempfile::tempdir_in(output.path()).unwrap();
        fs::write(staged.path().join("report.json"), b"new report").unwrap();
        fs::write(staged.path().join(crate::compiler_admission::FILE_NAME), b"new admission")
            .unwrap();
        commit_staged_report_bundle_with_hook(staged.path(), output.path(), |relative| {
            if relative == Path::new("report.json") {
                Err(io::Error::other("injected after admission install"))
            } else {
                Ok(())
            }
        })
        .unwrap_err();
        assert_eq!(fs::read(output.path().join("report.json")).unwrap(), b"old report");
        assert_eq!(
            fs::read(output.path().join(crate::compiler_admission::FILE_NAME)).unwrap(),
            b"old admission"
        );
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
            (crate::compiler_memory::FILE_NAME, "old-memory"),
            (crate::compiler_admission::FILE_NAME, "old-admission"),
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
            (crate::compiler_memory::FILE_NAME, "new-memory"),
            (crate::compiler_admission::FILE_NAME, "new-admission"),
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
            (crate::compiler_memory::FILE_NAME, "old-memory"),
            (crate::compiler_admission::FILE_NAME, "old-admission"),
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
        for name in [
            "report.ndjson",
            "report.html",
            "report.json",
            PROOF_UNSAFE_MEMORY_WRAPPER_FILE,
            crate::compiler_memory::FILE_NAME,
            crate::compiler_admission::FILE_NAME,
        ] {
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
    fn compiler_memory_sidecar_keeps_canonical_bytes_and_expires_with_its_bundle() {
        let report = report_with_result(result_with_location(None), VerificationOutcome::Proved)
            .to_trust_report();
        let output = tempfile::tempdir().expect("report output");
        let coverage = trust_types::CoverageTransportSummary {
            crate_name: "demo".to_string(),
            package_name: "demo".to_string(),
            primary_package: true,
            verification_session: "private-session".to_string(),
            eligible: 1,
            processed: 1,
            function_identities: None,
            noted_stops: Vec::new(),
            degraded_anchors: 0,
            memory: trust_types::MemorySummary::new([(
                trust_types::MemorySummary::SLOTS_COMPACTED.to_string(),
                3,
            )]),
        };
        let observations = [crate::compiler_memory::CompilerMemoryObservation::direct(&coverage)];
        write_report_artifacts_from_root_with_compiler_resources(
            &report,
            output.path(),
            "<html>trust</html>",
            None,
            None,
            None,
            CompilerResourceReports { memory: Some(&observations), ..Default::default() },
        )
        .expect("write report with memory observations");
        let canonical = fs::read(output.path().join("report.json")).unwrap();
        let sidecar_path = output.path().join(crate::compiler_memory::FILE_NAME);
        let sidecar: serde_json::Value =
            serde_json::from_slice(&fs::read(&sidecar_path).unwrap()).unwrap();
        assert_eq!(
            sidecar["proof_report_hash"],
            format!("sha256:{}", trust_types::digest::lowercase_hex(&Sha256::digest(&canonical)))
        );
        assert_eq!(sidecar["authority"], "observational_only_no_proof_credit");
        assert_eq!(sidecar["units"][0]["memory"]["counters"]["slots_compacted"], 3);
        assert!(!sidecar.to_string().contains("private-session"));

        write_report_artifacts(&report, output.path(), "<html>trust</html>")
            .expect("replace bundle without compiler observations");
        assert_eq!(fs::read(output.path().join("report.json")).unwrap(), canonical);
        assert!(!sidecar_path.exists(), "an old run's memory observations must not survive");
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
    fn artifact_only_capture_failure_revokes_an_already_reduced_live_measurement() {
        use crate::pipeline::run::{
            CompilerRunDiagnostics, ReportRendering, render_report_for_run,
        };
        let report = with_live_transport_authority(report_with_result(
            result_with_location(None),
            VerificationOutcome::Unknown,
        ));
        let live = report.sealed_canonical_report().expect("existing fixture's live seal");
        let measurement = crate::self_improve::measure_live_report("fixture", &live);
        let root = tempfile::tempdir().unwrap();
        let output = root.path().join("blocked");
        fs::write(&output, b"retained bytes").unwrap();
        let mut diagnostics = CompilerRunDiagnostics::default();
        let mut observe = |batch: &CompilerRunDiagnostics| diagnostics.extend(batch);
        let result = render_report_for_run(
            &report,
            ReportRendering::ArtifactsOnly,
            OutputFormat::Terminal,
            Some(output.to_str().unwrap()),
            None,
            true,
            CompilerResourceReports::default(),
            None,
            &mut Some(&mut observe),
        );
        assert!(result.is_err());
        assert!(diagnostics.artifact_failed);
        assert!(
            crate::self_improve::finish_measurement(
                Some(measurement),
                std::process::ExitCode::from(2),
                &diagnostics,
                true,
            )
            .is_err()
        );
        assert_eq!(fs::read(output).unwrap(), b"retained bytes");
    }

    #[test]
    fn artifact_only_capture_retains_the_live_measurement_and_full_report() {
        use crate::pipeline::run::{
            CompilerRunDiagnostics, ReportRendering, render_report_for_run,
        };
        let report = with_live_transport_authority(report_with_result(
            result_with_location(None),
            VerificationOutcome::Unknown,
        ));
        let live = report.sealed_canonical_report().expect("existing fixture's live seal");
        let measurement = crate::self_improve::measure_live_report("fixture", &live);
        let root = tempfile::tempdir().unwrap();
        let output = root.path().join("capture");
        let mut diagnostics = CompilerRunDiagnostics::default();
        let mut observe = |batch: &CompilerRunDiagnostics| diagnostics.extend(batch);
        let result = render_report_for_run(
            &report,
            ReportRendering::ArtifactsOnly,
            OutputFormat::Terminal,
            Some(output.to_str().unwrap()),
            None,
            true,
            CompilerResourceReports::default(),
            None,
            &mut Some(&mut observe),
        )
        .expect("artifact-only rendering succeeds through the existing sealed renderer");
        assert!(result.unwrap().complete);
        assert!(!diagnostics.artifact_failed);
        assert!(
            crate::self_improve::finish_measurement(
                Some(measurement),
                std::process::ExitCode::from(3),
                &diagnostics,
                true,
            )
            .is_ok(),
            "a genuine unknown verdict is still a completed measurement"
        );
        let retained: serde_json::Value =
            serde_json::from_slice(&fs::read(output.join("report.json")).unwrap()).unwrap();
        assert_eq!(retained["summary"]["total_unknown"], 1);
        assert_eq!(retained["summary"]["total_proved"], 0);
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
    fn unsafe_memory_wrapper_failed_rerun_invalidates_stale_success() {
        let repo = clean_git_repo("unsafe-memory-wrapper-stale");
        let output = tempfile::tempdir().expect("report output");
        let request = UnsafeMemoryReportRequest::new(repo.clone());
        let report = with_live_transport_authority(report_with_result(
            trust_vc_native_transport_result(),
            VerificationOutcome::Proved,
        ));
        let output_dir = output.path().to_str().expect("utf-8 report dir");

        report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(output_dir),
                Some(&request),
            )
            .expect("first clean run should publish wrapper");
        let wrapper = output.path().join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE);
        assert!(wrapper.is_file());

        fs::write(repo.join("dirty.rs"), "unsafe fn changed() {}\n")
            .expect("change source after first report");
        let error = report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(output_dir),
                Some(&request),
            )
            .expect_err("dirty rerun must refuse publication");
        assert!(error.to_string().contains("repo must be clean"), "{error}");
        assert!(!wrapper.exists(), "failed rerun left an old success-shaped wrapper");
        assert!(
            output.path().join("report.json").is_file(),
            "ordinary report remains observational"
        );

        let _ = fs::remove_dir_all(repo);
    }

    #[test]
    fn unsafe_memory_wrapper_invalid_repo_root_invalidates_stale_success() {
        let repo = clean_git_repo("unsafe-memory-wrapper-invalid-root");
        let output = tempfile::tempdir().expect("report output");
        let wrapper = output.path().join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE);
        let report = with_live_transport_authority(report_with_result(
            trust_vc_native_transport_result(),
            VerificationOutcome::Proved,
        ));
        let output_dir = output.path().to_str().expect("utf-8 report dir");
        report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(output_dir),
                Some(&UnsafeMemoryReportRequest::new(repo.clone())),
            )
            .expect("valid first run should publish wrapper");
        assert!(wrapper.is_file());

        let nested = repo.join("nested");
        fs::create_dir(&nested).expect("create non-root request path");
        let request = UnsafeMemoryReportRequest::new(nested);

        let error = report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(output_dir),
                Some(&request),
            )
            .expect_err("non-root request must refuse after safe cleanup");
        assert!(error.to_string().contains("exact Git top level"), "{error}");
        assert!(!wrapper.exists(), "invalid-root rerun left a success-shaped wrapper");
        assert!(output.path().join("report.json").is_file());

        let _ = fs::remove_dir_all(repo);
    }

    #[test]
    fn unsafe_memory_wrapper_invalid_repo_root_does_not_delete_tracked_output() {
        let repo = clean_git_repo("unsafe-memory-wrapper-invalid-root-tracked");
        let tracked_output = repo.join("tracked-output");
        fs::create_dir(&tracked_output).expect("create tracked output directory");
        let wrapper = tracked_output.join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE);
        fs::write(&wrapper, "tracked-source-sentinel").expect("write tracked wrapper");
        run_git(&repo, &["add", "-A"]);
        run_git(&repo, &["commit", "-m", "tracked output fixture"]);
        let nested = repo.join("nested");
        fs::create_dir(&nested).expect("create non-root request path");
        let request = UnsafeMemoryReportRequest::new(nested);

        let error = invalidate_previous_unsafe_memory_wrapper(&request, &tracked_output)
            .expect_err("invalid root must not permit cleanup of tracked source");
        assert!(error.to_string().contains("tracked source files"), "{error}");
        assert_eq!(fs::read_to_string(wrapper).unwrap(), "tracked-source-sentinel");

        let _ = fs::remove_dir_all(repo);
    }

    #[test]
    fn unsafe_memory_wrapper_unresolvable_repo_root_retains_unvalidated_output() {
        let no_repo = tempfile::tempdir().expect("non-repository root");
        let output = tempfile::tempdir().expect("report output");
        let wrapper = output.path().join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE);
        fs::write(&wrapper, "unvalidated-wrapper").expect("write earlier wrapper");
        let request = UnsafeMemoryReportRequest::new(no_repo.path().to_path_buf());

        invalidate_previous_unsafe_memory_wrapper(&request, output.path())
            .expect_err("root without a controlled Git worktree must refuse cleanup");
        assert_eq!(fs::read_to_string(wrapper).unwrap(), "unvalidated-wrapper");
    }

    #[cfg(unix)]
    #[test]
    fn unsafe_memory_wrapper_unlink_stays_on_open_directory_after_parent_swap() {
        use std::os::unix::fs::symlink;

        let repo = clean_git_repo("unsafe-memory-wrapper-unlink-swap");
        let tracked_parent = repo.join("tracked-parent");
        let tracked_output = tracked_parent.join("proof");
        fs::create_dir_all(&tracked_output).expect("create tracked target directory");
        let tracked_wrapper = tracked_output.join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE);
        fs::write(&tracked_wrapper, "tracked-source-sentinel")
            .expect("write tracked target wrapper");
        run_git(&repo, &["add", "-A"]);
        run_git(&repo, &["commit", "-m", "tracked target fixture"]);

        let outside = tempfile::tempdir().expect("output parent");
        let parent = outside.path().join("parent");
        let output = parent.join("proof");
        fs::create_dir_all(&output).expect("create original output directory");
        fs::write(output.join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE), "stale-wrapper")
            .expect("write original stale wrapper");
        let moved_parent = outside.path().join("moved-parent");
        let request = UnsafeMemoryReportRequest::new(repo.clone());

        invalidate_previous_unsafe_memory_wrapper_with_hook(&request, &output, || {
            fs::rename(&parent, &moved_parent)?;
            symlink(&tracked_parent, &parent)?;
            Ok(())
        })
        .expect("unlink must use the opened directory after parent replacement");
        assert_eq!(fs::read_to_string(tracked_wrapper).unwrap(), "tracked-source-sentinel");
        assert!(!moved_parent.join("proof").join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE).exists());

        let _ = fs::remove_dir_all(repo);
    }

    #[cfg(unix)]
    #[test]
    fn unsafe_memory_wrapper_cleanup_rejects_parent_alias_to_tracked_output() {
        use std::os::unix::fs::symlink;

        let repo = clean_git_repo("unsafe-memory-wrapper-parent-alias");
        let tracked_output = repo.join("tracked-output");
        fs::create_dir(&tracked_output).expect("create tracked output directory");
        let tracked_wrapper = tracked_output.join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE);
        fs::write(&tracked_wrapper, "tracked-source-sentinel")
            .expect("write tracked wrapper fixture");
        run_git(&repo, &["add", "-A"]);
        run_git(&repo, &["commit", "-m", "tracked output fixture"]);

        let alias_parent = tempfile::tempdir().expect("alias parent");
        let alias = alias_parent.path().join("repo-alias");
        symlink(&repo, &alias).expect("alias repository through parent symlink");
        let alias_output = alias.join("tracked-output");
        let request = UnsafeMemoryReportRequest::new(repo.clone());
        let report = with_live_transport_authority(report_with_result(
            trust_vc_native_transport_result(),
            VerificationOutcome::Proved,
        ));

        let error = report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(alias_output.to_str().expect("utf-8 alias path")),
                Some(&request),
            )
            .expect_err("tracked source behind a parent alias must not be removed");
        assert!(error.to_string().contains("tracked source files"), "{error}");
        assert_eq!(fs::read_to_string(tracked_wrapper).unwrap(), "tracked-source-sentinel");

        let _ = fs::remove_dir_all(repo);
    }

    #[test]
    fn unsafe_memory_wrapper_rejects_tracked_output_with_pathspec_metacharacters() {
        let repo = clean_git_repo("unsafe-memory-wrapper-literal-output");
        let output_dir = repo.join("report[1]");
        fs::create_dir(&output_dir).expect("create tracked output directory");
        fs::write(output_dir.join("tracked.txt"), "source\n").expect("write tracked source");
        run_git(&repo, &["add", "-A"]);
        run_git(&repo, &["commit", "-m", "tracked output fixture"]);

        let error = validated_output_exclusion(&repo, &output_dir)
            .expect_err("tracked output must be rejected even with pathspec metacharacters");
        assert!(error.to_string().contains("tracked source files"), "{error}");

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
    fn unsafe_memory_coverage_rejects_duplicate_obligation_id() {
        let row = trust_vc_native_transport_result();
        let mut report = report_with_result(row.clone(), VerificationOutcome::Proved);
        report.results.push(row);

        let error = unsafe_memory_coverage(&report, &AuthorizedRows { results: &report.results })
            .expect_err("duplicate emitted obligations must not enter the wrapper");
        assert!(error.to_string().contains("duplicate unsafe-memory obligation id"), "{error}");
    }

    #[test]
    fn unsafe_memory_coverage_rejects_unowned_result() {
        let mut row = trust_vc_native_transport_result();
        row.function = "unknown".into();
        let report = report_with_result(row, VerificationOutcome::Proved);

        let error = unsafe_memory_coverage(&report, &AuthorizedRows { results: &report.results })
            .expect_err("unowned emitted obligations must not enter the wrapper");
        assert!(error.to_string().contains("has no function owner"), "{error}");
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
            text_error.to_string().contains("lacks a structured obligation id"),
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
        let result = transport_to_verification_result(
            "crate::trust_vc_memory_owner",
            &transport,
            None,
            None,
        );
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
            identity: None,
            obligation_id: evidence.obligation_id,
            claim_digest_sha256: evidence.claim_digest_sha256,
            original_vc_snapshot: evidence.original_vc_snapshot,
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
        let owner = "trust_ir-native-trust-mc-request-7-proof-42";
        let native_id = "trust_ir-native-trust-mc-request-7-proof-42";
        let input = bound_test_artifact(
            "NormalizedObligation",
            b"exact normalized trust-mc obligation",
            native_id,
            owner,
            vec![],
        );
        let transcript = bound_test_artifact(
            "SolverTranscript",
            b"exact trust-mc solver transcript",
            native_id,
            owner,
            vec![trust_types::TransportArtifactReference {
                kind: input.kind.clone(),
                digest: input.digest.clone().expect("input digest"),
            }],
        );
        let check = bound_test_artifact(
            "ProofCheckReport",
            b"exact trust-mc proof-check report",
            native_id,
            owner,
            vec![trust_types::TransportArtifactReference {
                kind: transcript.kind.clone(),
                digest: transcript.digest.clone().expect("transcript digest"),
            }],
        );
        trust_types::TransportObligationResult {
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: Some(owner.into()),
            claim_digest_sha256: Some(
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into(),
            ),
            kind: "postcond".into(),
            original_vc_snapshot: None,
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
            solver: "trust-mc".into(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: Some("native full verifier status: Proved".into()),
            design_mandate: false,
            native_trust_ir: Some(trust_types::TransportNativeTrustIrEvidence {
                suite: "trust-mc".into(),
                backend: "trust-mc".into(),
                request_id: Some("7".into()),
                native_id: Some("trust_ir-native-trust-mc-request-7-proof-42".into()),
                present: true,
                artifacts: native_trust_ir_shape_artifacts("trust-mc", "7", "42"),
                diagnostics: vec![trust_types::TransportEvidenceDiagnostic {
                    code: "native_trust_ir.accepted".into(),
                    severity: trust_types::TransportEvidenceDiagnosticSeverity::Info,
                    message: "typed TrustIr native request accepted".into(),
                    detail: Some("suite=trust-mc request_id=7 proof_obligation_id=42".into()),
                }],
            }),
            proof_evidence: Some(trust_types::TransportProofEvidence {
                suite: "trust-mc".into(),
                backend: "trust-mc".into(),
                request_id: Some("7".into()),
                proof_id: Some("42".into()),
                native_id: Some("trust_ir-native-trust-mc-request-7-proof-42".into()),
                status: trust_types::TransportProofStatus::Proved,
                strength: Some(ProofStrength::deductive()),
                evidence: Some(trust_types::ProofEvidence::from(ProofStrength::deductive())),
                artifacts: vec![input, transcript, check],
                diagnostics: vec![trust_types::TransportEvidenceDiagnostic {
                    code: "suite.accepted".into(),
                    severity: trust_types::TransportEvidenceDiagnosticSeverity::Info,
                    message: "trust-mc suite produced accepted proof evidence".into(),
                    detail: Some("primary owner trust-mc@7".into()),
                }],
            }),
            monitor: None,
            grade: None,
        }
    }

    fn native_full_verifier_transport_result() -> VerificationResult {
        let transport = native_full_verifier_transport();
        transport_to_verification_result("crate::checked_contract", &transport, None, None)
    }

    /// The bytes the compiler content-addresses a CleanCic payload by
    /// (`compiler/rustc_mir_transform/src/trust_verify.rs`: `to_vec` of
    /// `to_value(evidence)`, in a crate graph with `serde_json/preserve_order`,
    /// so the fields stay in declaration order). Written out from the typed
    /// value, never through a `Value`, so this test helper produces the
    /// compiler's bytes in a build of targo-trust alone too, where a `Value`
    /// re-serializes key-sorted. The sorted order differs (`context` first), so
    /// a consumer that hashed its re-serialized `Value` refuses these rows in
    /// that build (CLEAN-CIC-TYPED-ADDRESS-1).
    fn compiler_clean_cic_payload_bytes(evidence: &trust_ir::ProofEvidence) -> Vec<u8> {
        let bytes = serde_json::to_vec(evidence).expect("serialize CleanCic test payload");
        let text = std::str::from_utf8(&bytes).expect("JSON is UTF-8");
        assert!(
            text.starts_with("{\"CleanCic\":{\"term\":"),
            "the compiler's bytes keep declaration order: {text}"
        );
        bytes
    }

    fn clean_cic_hardened_transport() -> trust_types::TransportObligationResult {
        // Exact held payload bytes, matching the compiler's v2 publication
        // shape: the outer proof and its sole artifact are both addressed by
        // the framed digest of the certificate's serialized bytes.
        let evidence = trust_ir::ProofEvidence::CleanCic {
            term: vec![1, 2, 3, 5, 8],
            context: vec![13, 21],
            lineage: trust_ir::ProofDigest::sha256([0xab; 32]),
            kernel_recheck: None,
        };
        let payload =
            serde_json::to_value(&evidence).expect("serialize typed CleanCic test payload");
        let bytes = compiler_clean_cic_payload_bytes(&evidence);
        let digest = trustc_domain_length_bound_sha256_hex("trustc.transport-clean-cic.v2", &bytes);
        let proof_id = format!("clean-cic:v2:{digest}");
        let strength = ProofStrength {
            reasoning: trust_types::ReasoningKind::Constructive,
            assurance: trust_types::AssuranceLevel::Certified,
        };

        trust_types::TransportObligationResult {
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: Some("crate::paths::render:hardened-cleancic".into()),
            claim_digest_sha256: Some(
                "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".into(),
            ),
            kind: "hardened_byte_loss".into(),
            original_vc_snapshot: None,
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
                // KR0 switch: a clean-kernel row names the reference theory.
                evidence: Some(trust_types::ProofEvidence::from(strength).with_kernel_reference(
                    trust_types::KernelTheoryId::LeanReferenceV1,
                    trust_types::KernelEnvDigest([0x2a; 32]),
                )),
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
            grade: None,
        }
    }

    fn clean_cic_hardened_result() -> VerificationResult {
        let transport = clean_cic_hardened_transport();
        transport_to_verification_result("crate::paths::render", &transport, None, None)
    }

    fn promoted_proof_evidence_for_transport(
        transport: trust_types::TransportObligationResult,
    ) -> Option<ObligationProofEvidenceReport> {
        let result =
            transport_to_verification_result("crate::checked_contract", &transport, None, None);
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let trust_report = report.to_trust_report();
        trust_report.functions[0].obligations[0].proof_evidence.clone()
    }

    /// The EXACT `termination` row the sealed compiler `trust-fbd7fbfe`
    /// transported for `fact` in the p5_recursion reproduction (`fn fact(n:
    /// u32) -> Option<u64>` recursing on `n - 1`), captured with
    /// `-Ztrust-verify-output=json -Ztrust-proof-artifact-root=<0700 dir>` and
    /// with the three path-backed native-bundle materializations inlined
    /// byte-for-byte (digests re-verified) so the fixture needs no root (its
    /// coverage row's `memory` summary was added by hand in T3 L4 C09w, with no counters:
    /// the reproduction's source is not in the tree, so it cannot be recaptured). Its
    /// proof is a trust-mc typed-CHC/PDR proof with a SolverTranscript,
    /// ProofCheckReport, ReplayLog and Model, all bound to
    /// `trust_ir-native-trust-mc-request-2-proof-2`; strength `{Pdr, Sound}`
    /// and evidence transported as `{Pdr, Sound}` — the legacy spelling of
    /// `ProofEvidence::from(ProofStrength::pdr()) == {Pdr, SmtBacked}`.
    fn real_trust_mc_pdr_termination_transport() -> (String, trust_types::TransportObligationResult)
    {
        let transport = include_str!("fixtures/p5_recursion_termination_pdr_transport.jsonl");
        for line in transport.lines() {
            let Some(message) = trust_types::parse_transport_line(line.trim()) else {
                continue;
            };
            if let trust_types::TransportMessage::FunctionResult(func_result) = message {
                for row in &func_result.results {
                    if row.kind == "termination" {
                        return (func_result.function.clone(), row.clone());
                    }
                }
            }
        }
        panic!("fixture carries no termination row");
    }

    /// Trust (2026-09-16, T4): the real row, captured from the sealed
    /// `trust-acb74dd5` compiler (`-Z trust-verify-output=json` on the battery's
    /// `p7_helper_print.rs`): the closure `|| "world".to_string()`'s
    /// whole-function panic-freedom row, `Proved` by the compiler's
    /// interprocedural callee closure (`trust-assert-refute`; TCB class
    /// `Trusted`) — exact claim digest, typed `Assertion`, and NO proof
    /// evidence, because that authority's premises (the Session's panic-free
    /// callee registry) are not attachable.
    fn real_p7_closure_assert_refute_transport() -> (String, trust_types::TransportObligationResult)
    {
        let transport = include_str!("fixtures/p7_closure_assert_refute_transport.jsonl");
        for line in transport.lines() {
            let Some(message) = trust_types::parse_transport_line(line.trim()) else {
                continue;
            };
            if let trust_types::TransportMessage::FunctionResult(func_result) = message {
                if let Some(row) = func_result.results.first() {
                    return (func_result.function.clone(), row.clone());
                }
            }
        }
        panic!("fixture carries no row");
    }

    /// Run one real compiler row through the exact production publication
    /// path (`normalize_authenticated_results_for_publication` + live
    /// transport authority + canonical report rendering), with no artifact
    /// root — every artifact in the fixture is inline.
    fn rendered_real_row(
        function: &str,
        transport: trust_types::TransportObligationResult,
    ) -> (trust_types::ObligationReport, crate::types::PublicationBoundary) {
        let result = transport_to_verification_result(function, &transport, None, None);
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let boundary = report.publication_boundary.clone().expect("publication boundary");
        let obligation = report.to_trust_report().functions.remove(0).obligations.remove(0);
        (obligation, boundary)
    }

    // The current v2 body family (61bfe9fb8f): the positive control and the
    // base every tamper mutation below starts from, so a refusal there is the
    // mutation's doing and not the fixture's.
    fn real_native_body_wp_transport() -> trust_types::TransportObligationResult {
        serde_json::from_str::<Vec<trust_types::TransportObligationResult>>(include_str!(
            "../../crates/trust-types/tests/fixtures/native_body_wp_current_v2_transport.json"
        ))
        .expect("actual compiler transport array")
        .remove(0)
    }

    #[test]
    fn historical_v1_native_body_wp_certificate_is_withheld_from_publication() {
        let transport = serde_json::from_str::<Vec<trust_types::TransportObligationResult>>(
            include_str!("../../crates/trust-types/tests/fixtures/native_body_wp_transport.json"),
        )
        .expect("historical v1 compiler transport array")
        .remove(0);
        let (obligation, boundary) = rendered_real_row("wp_query_source::identity", transport);
        assert!(
            matches!(obligation.outcome, ObligationOutcome::Unknown { .. }),
            "{:?}",
            obligation.outcome
        );
        assert!(obligation.proof_evidence.is_none());
        assert_eq!(boundary.withheld_relabelled, 1);
        assert_eq!(boundary.published_favorable, 0);
    }

    #[test]
    fn actual_native_body_wp_certificate_publishes_without_rebinding() {
        let transport = real_native_body_wp_transport();
        let original_artifacts = transport.proof_evidence.as_ref().unwrap().artifacts.clone();
        let (obligation, boundary) =
            rendered_real_row("wp_query_source::identity", transport.clone());
        assert!(
            matches!(obligation.outcome, ObligationOutcome::Proved { .. }),
            "{:?}",
            obligation.outcome
        );
        assert_eq!(boundary.withheld_relabelled, 0);
        assert_eq!(boundary.published_favorable, 1);
        let proof = obligation.proof_evidence.as_ref().unwrap();
        assert_eq!(proof.strength, ProofStrength::deductive());
        assert_eq!(proof.evidence, ProofEvidence::from(ProofStrength::deductive()));
        assert_eq!(
            proof.artifacts, original_artifacts,
            "accepted certificate bytes and owner binding are immutable"
        );
        assert_eq!(trust_types::saved_obligation_structural_proof_defect(&obligation, None), None);

        let result =
            transport_to_verification_result("wp_query_source::identity", &transport, None, None);
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let wire = serde_json::to_vec(&report.to_trust_report()).unwrap();
        let (loaded, sanitization, _) =
            trust_types::JsonProofReport::decode_saved_json(&wire, None).unwrap();
        assert_eq!(sanitization.downgraded_proved, 1);
        assert_eq!(sanitization.structural_evidence_defects, 0);
        assert!(matches!(
            loaded.functions[0].obligations[0].outcome,
            ObligationOutcome::Unknown { .. }
        ));
    }

    #[test]
    fn actual_native_body_wp_certificate_rejects_legacy_and_tampered_publication() {
        for mutation in 0..6 {
            let mut transport = real_native_body_wp_transport();
            let proof = transport.proof_evidence.as_mut().unwrap();
            match mutation {
                0 => transport.obligation_id = Some("other-public-owner".into()),
                1 => proof.request_id = Some("4".into()),
                2 => proof.artifacts.push(proof.artifacts[0].clone()),
                3 => proof.artifacts[0].kind = "SolverTranscript".into(),
                4 => {
                    proof.strength.as_mut().unwrap().assurance = AssuranceLevel::Certified;
                    proof.evidence.as_mut().unwrap().assurance = AssuranceLevel::Certified;
                }
                _ => proof.artifacts[0]
                    .materialization
                    .as_mut()
                    .unwrap()
                    .encoded_bytes
                    .replace_range(0..2, "00"),
            }
            let (obligation, boundary) = rendered_real_row("wp_query_source::identity", transport);
            assert!(
                matches!(obligation.outcome, ObligationOutcome::Unknown { .. }),
                "mutation {mutation}: {:?}",
                obligation.outcome
            );
            assert!(obligation.proof_evidence.is_none(), "mutation {mutation}");
            assert_eq!(boundary.withheld_relabelled, 1, "mutation {mutation}");
        }
    }

    /// Measured 2026-09-16 on `trust-fbd7fbfe`: this row was the ONLY thing
    /// between the p5_recursion program and PASS. Every conjunct of
    /// `structured_native_proof_is_publishable` held at the real artifact root
    /// (identity, binding, publication-grade strength AND evidence, artifact
    /// topology, native bundle shape, diagnostics) except one — the exact
    /// equality `evidence == ProofEvidence::from(strength)`, which compared
    /// `{Pdr, Sound}` against `{Pdr, SmtBacked}`: the same rung of the
    /// assurance ladder under two spellings. The publication boundary now
    /// compares both records through the one canonical mapping and publishes
    /// the canonical spelling, so the emitted obligation also satisfies
    /// trust-types' saved-report structural validator.
    #[test]
    fn real_trust_mc_pdr_row_with_legacy_sound_evidence_publishes() {
        let (function, transport) = real_trust_mc_pdr_termination_transport();
        let transported = transport.proof_evidence.as_ref().expect("proof evidence");
        assert_eq!(transported.strength, Some(ProofStrength::pdr()), "control: strength is PDR");
        assert_eq!(
            transported.evidence,
            Some(trust_types::ProofEvidence::new(
                trust_types::ReasoningKind::Pdr,
                trust_types::AssuranceLevel::Sound
            )),
            "control: the compiler transported the LEGACY evidence spelling"
        );
        assert_ne!(
            transported.evidence,
            Some(trust_types::ProofEvidence::from(ProofStrength::pdr())),
            "control: the legacy spelling is not byte-equal to the canonical one"
        );

        let (obligation, boundary) = rendered_real_row(&function, transport);

        assert!(
            matches!(obligation.outcome, ObligationOutcome::Proved { .. }),
            "the row must publish as Proved; got {:?}",
            obligation.outcome
        );
        assert_eq!(boundary.withheld_relabelled, 0);
        assert_eq!(boundary.published_favorable, 1);
        let proof = obligation.proof_evidence.as_ref().expect("published proof evidence");
        assert_eq!(proof.strength, ProofStrength::pdr());
        assert_eq!(
            proof.evidence,
            trust_types::ProofEvidence::from(ProofStrength::pdr()),
            "the published evidence is the canonical spelling"
        );
        assert_eq!(proof.native_id.as_deref(), Some("trust_ir-native-trust-mc-request-2-proof-2"));
        assert!(proof.artifacts.iter().any(is_replay_or_check_artifact));
        assert!(proof.artifacts.iter().any(is_solver_transcript_artifact));
        // The envelope's copy of the proof record is ELIDED on a published
        // proved row (`elide_duplicate_transport_proof_evidence`), and the
        // producer drops it only after the decoder's own field-for-field
        // comparison agreed, which includes `evidence` and `strength`. So its
        // absence is the proof that the envelope carried the canonical
        // spelling too; the legacy spelling would have kept the copy.
        let envelope = obligation.transport_evidence.as_ref().expect("transport envelope");
        assert!(
            envelope.proof_evidence.is_none(),
            "the envelope's duplicate proof record must be elided once it matches the \
             published record"
        );
        assert_eq!(
            trust_types::saved_obligation_structural_proof_defect(&obligation, None),
            None,
            "the emitted obligation must pass trust-types' saved-report contract"
        );
    }

    /// The loosening is exact: the same real row is still WITHHELD when its
    /// proof DAG loses the replay/check consumer, when its native binding id
    /// disagrees, when one artifact's proof-binding disagrees, and when the
    /// evidence record genuinely disagrees with the strength record — a
    /// different reasoning kind, or an assurance on a different rung.
    #[test]
    fn real_trust_mc_pdr_row_is_still_withheld_on_every_genuine_defect() {
        let (function, transport) = real_trust_mc_pdr_termination_transport();
        let (control, _) = rendered_real_row(&function, transport.clone());
        assert!(matches!(control.outcome, ObligationOutcome::Proved { .. }), "control publishes");

        let withheld =
            |label: &str, mutate: &dyn Fn(&mut trust_types::TransportObligationResult)| {
                let mut mutated = transport.clone();
                mutate(&mut mutated);
                let (obligation, boundary) = rendered_real_row(&function, mutated);
                assert!(
                    matches!(obligation.outcome, ObligationOutcome::Unknown { .. }),
                    "{label}: must be withheld; got {:?}",
                    obligation.outcome
                );
                assert!(obligation.proof_evidence.is_none(), "{label}: no proof evidence");
                assert_eq!(boundary.withheld_relabelled, 1, "{label}: boundary discloses it");
            };

        withheld("no replay/check consumer", &|row| {
            row.proof_evidence
                .as_mut()
                .expect("proof evidence")
                .artifacts
                .retain(|artifact| !is_replay_or_check_artifact(artifact));
        });
        withheld("native_id mismatch", &|row| {
            row.proof_evidence.as_mut().expect("proof evidence").native_id =
                Some("trust_ir-native-trust-mc-request-2-proof-3".into());
        });
        withheld("artifact proof_binding_id mismatch", &|row| {
            let proof = row.proof_evidence.as_mut().expect("proof evidence");
            let transcript = proof
                .artifacts
                .iter_mut()
                .find(|artifact| is_solver_transcript_artifact(artifact))
                .expect("solver transcript");
            transcript.materialization.as_mut().expect("materialization").proof_binding_id =
                "trust_ir-native-trust-mc-request-2-proof-3".into();
        });
        withheld("evidence reasoning disagrees with strength", &|row| {
            row.proof_evidence.as_mut().expect("proof evidence").evidence =
                Some(trust_types::ProofEvidence::new(
                    trust_types::ReasoningKind::Smt,
                    trust_types::AssuranceLevel::Sound,
                ));
        });
        withheld("evidence claims Certified over a Sound strength", &|row| {
            row.proof_evidence.as_mut().expect("proof evidence").evidence =
                Some(trust_types::ProofEvidence::new(
                    trust_types::ReasoningKind::Pdr,
                    trust_types::AssuranceLevel::Certified,
                ));
        });
        withheld("evidence claims Trusted over a Sound strength", &|row| {
            row.proof_evidence.as_mut().expect("proof evidence").evidence =
                Some(trust_types::ProofEvidence::new(
                    trust_types::ReasoningKind::Pdr,
                    trust_types::AssuranceLevel::Trusted,
                ));
        });
        withheld("evidence record missing", &|row| {
            row.proof_evidence.as_mut().expect("proof evidence").evidence = None;
        });
    }

    fn trust_vc_native_transport_result() -> VerificationResult {
        let seed_digest = "6666666666666666666666666666666666666666666666666666666666666666";
        let transport = trust_vc_certificate_only_transport(
            format!("{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{seed_digest}.json"),
            seed_digest,
        );
        transport_to_verification_result("crate::trust_vc_memory_owner", &transport, None, None)
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
        let native_id = "trust_ir-native-trust-mc-request-8-proof-9";
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
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: Some(owner.into()),
            claim_digest_sha256: Some(
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
            ),
            kind: "hardened_byte_loss".into(),
            original_vc_snapshot: None,
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
            solver: "trust-mc".into(),
            time_ms: 4,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: Some(trust_types::TransportNativeTrustIrEvidence {
                suite: "trust-mc".into(),
                backend: "trust-mc".into(),
                request_id: Some("8".into()),
                native_id: Some("trust_ir-native-trust-mc-request-8-proof-9".into()),
                present: true,
                artifacts: native_trust_ir_shape_artifacts("trust-mc", "8", "9"),
                diagnostics: vec![trust_types::TransportEvidenceDiagnostic {
                    code: "unix.model_assumption".into(),
                    severity: trust_types::TransportEvidenceDiagnosticSeverity::Info,
                    message: "model assumption: Unix OsStr preserves raw bytes at boundary".into(),
                    detail: Some("argv/env/path bytes remain byte-exact".into()),
                }],
            }),
            proof_evidence: Some(trust_types::TransportProofEvidence {
                suite: "trust-mc".into(),
                backend: "trust-mc".into(),
                request_id: Some("8".into()),
                proof_id: Some("9".into()),
                native_id: Some("trust_ir-native-trust-mc-request-8-proof-9".into()),
                status: TransportProofStatus::Proved,
                strength: Some(ProofStrength::deductive()),
                evidence: Some(trust_types::ProofEvidence::from(ProofStrength::deductive())),
                artifacts: vec![input, transcript, check],
                diagnostics: Vec::new(),
            }),
            monitor: None,
            grade: None,
        };
        transport_to_verification_result("crate::paths::render", &transport, None, None)
    }

    fn unsafe_demand_row(backend: &str, outcome: VerificationOutcome) -> VerificationResult {
        VerificationResult {
            function: "crate::hsum".into(),
            kind: "hardened_unsafe_operation".into(),
            message: "assertion: [unsafe:unmodeled-call] call to `vpaddq_f32` (unsafe fn) is not \
                      covered by Trust's model"
                .into(),
            outcome,
            backend: backend.into(),
            time_ms: Some(0),
            location: None,
            counterexample: None,
            reason: None,
            raw_line: String::new(),
        }
    }

    #[test]
    fn terminal_labels_a_fail_closed_unsafe_row_unproved_not_refuted() {
        let label = trust_types::UNSAFE_DEMAND_FAIL_CLOSED_SOLVER;
        let row = unsafe_demand_row(label, VerificationOutcome::Failed);
        let line = terminal_result_line(&row);
        assert!(
            line.starts_with("  [FAILED: unproved, no counterexample; failed closed] [hardened_unsafe_operation] "),
            "{line}"
        );
        // CONTROL: a refuted row renders exactly as before.
        let refuted = unsafe_demand_row("ay", VerificationOutcome::Failed);
        assert!(
            terminal_result_line(&refuted).starts_with("  [FAILED] [hardened_unsafe_operation] ")
        );
        // A counterexample is a refutation whatever the label says.
        let mut with_cex = row.clone();
        with_cex.counterexample = Some(trust_types::Counterexample::new(vec![(
            "x".into(),
            trust_types::CounterexampleValue::Uint(1),
        )]));
        assert!(terminal_result_line(&with_cex).starts_with("  [FAILED] "));
    }

    #[test]
    fn fail_closed_unsafe_rows_leave_the_gate_partition_unchanged() {
        let label = trust_types::UNSAFE_DEMAND_FAIL_CLOSED_SOLVER;
        let rows = vec![
            unsafe_demand_row(label, VerificationOutcome::Failed),
            unsafe_demand_row(label, VerificationOutcome::Failed),
            unsafe_demand_row("ay", VerificationOutcome::Failed),
            unsafe_demand_row(label, VerificationOutcome::Unknown),
        ];
        // CONTROL: the same rows with every label a plain refuting backend.
        let control: Vec<_> = rows
            .iter()
            .map(|row| VerificationResult { backend: "ay".into(), ..row.clone() })
            .collect();
        let (counts, _) = crate::pipeline::hardened::partition_outcome_counts(&rows);
        let (control_counts, _) = crate::pipeline::hardened::partition_outcome_counts(&control);
        assert_eq!(counts, control_counts, "the exit-code gate's partition must not move");
        assert_eq!(counts.failed, 3);
        // Only the two failed rows carrying the label are unproved; the unknown
        // row is not a failure at all.
        assert_eq!(failed_unproved_rows(&rows), 2);
        assert_eq!(failed_unproved_rows(&control), 0);
        let line = failed_unproved_terminal_line(&rows, counts.failed).expect("a split line");
        assert!(
            line.starts_with("Failed rows: 3 failed, 2 of them unproved with NO counterexample"),
            "{line}"
        );
        assert!(failed_unproved_terminal_line(&control, control_counts.failed).is_none());
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
            Some("trust_ir-native-trust-mc-request-7-proof-42")
        );
        assert_eq!(obligation.solver, "trust-mc");
        assert_eq!(obligation.kind, "postcondition");
        assert_eq!(obligation.proof_level, trust_types::ProofLevel::L1Functional);
        assert_eq!(obligation.description, "postcondition");
        let evidence = obligation.proof_evidence.as_ref().expect("full verifier evidence");
        assert_eq!(evidence.suite.as_deref(), Some("trust-mc"));
        assert_eq!(evidence.backend, "trust-mc");
        assert_eq!(evidence.request_id.as_deref(), Some("7"));
        assert_eq!(evidence.proof_id.as_deref(), Some("42"));
        assert_eq!(
            evidence.native_id.as_deref(),
            Some("trust_ir-native-trust-mc-request-7-proof-42")
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
                assert_eq!(verifier, "trust-mc");
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
            "trust_ir-native-trust-mc-request-7-proof-42"
        );
        assert_eq!(
            json["functions"][0]["obligations"][0]["proof_evidence"]["strength"]["reasoning"],
            "Deductive"
        );
        assert_eq!(json["functions"][0]["obligations"][0]["proof_evidence"]["suite"], "trust-mc");
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

        let result =
            transport_to_verification_result("crate::checked_contract", &transport, None, None);
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

            let result =
                transport_to_verification_result("crate::checked_contract", &transport, None, None);
            assert_eq!(result.outcome, expected, "nested status {status:?}");
            assert!(
                result.reason.is_none(),
                "typed-kind diagnostics must not overwrite a nested hard outcome"
            );
        }
    }

    /// Determinism plan §3.7 (2026-10-01): a full-verifier row the compiler
    /// published `timeout` is a clock stop and stays one whatever its native
    /// evidence says — `unsupported` (a bundle the deadline declined),
    /// `unknown` (a row the bridge never reached), `proved` (a row whose live
    /// mint the deadline refused) — so `add_verification_result_count` counts
    /// it in the function's `timed_out` and its row keeps the
    /// `[stop:wall-backstop]` reason. FAILS on the pre-fix tree: each of the
    /// first four read `Unknown`. A refutation in the evidence still outranks
    /// the clock.
    #[test]
    fn full_verifier_clock_stop_keeps_its_timeout_over_undecided_evidence() {
        use trust_types::determinism::StopCause;
        let clock_stop = |status: trust_types::TransportProofStatus| {
            let mut transport = native_full_verifier_transport();
            transport.outcome = trust_types::Outcome::Timeout;
            transport.solver = "trust-full-verifier".into();
            transport.time_ms = 120_000;
            transport.reason = Some(StopCause::WallBackstop.stamp("solver timed out"));
            transport.proof_evidence.as_mut().expect("proof evidence").status = status;
            transport_to_verification_result("crate::checked_contract", &transport, None, None)
        };
        for status in [
            trust_types::TransportProofStatus::Unsupported,
            trust_types::TransportProofStatus::Unknown,
            trust_types::TransportProofStatus::Proved,
            trust_types::TransportProofStatus::Rejected,
            trust_types::TransportProofStatus::Timeout,
        ] {
            let result = clock_stop(status);
            assert_eq!(result.outcome, VerificationOutcome::Timeout, "nested status {status:?}");
            assert_eq!(
                result.reason.as_deref().and_then(StopCause::from_reason),
                Some(StopCause::WallBackstop),
                "nested status {status:?}: the row still says a clock stopped it"
            );
        }
        assert_eq!(
            clock_stop(trust_types::TransportProofStatus::Failed).outcome,
            VerificationOutcome::Failed,
            "a refutation is never softened into a timeout"
        );
    }

    #[test]
    fn a_refutation_the_compiler_withheld_is_not_published_as_failed() {
        // The compiler reports `unknown` when it withholds a solver model that
        // is not an execution (DQ D5-A, loop-carried state), while the native
        // evidence still carries the engine's `failed`. The compiler decides what
        // is a refutation: the row is Unknown, never Failed, and never proved.
        let mut transport = native_full_verifier_transport();
        transport.outcome = trust_types::Outcome::Unknown;
        transport.solver = "trust-full-verifier".into();
        transport.reason = Some(
            "generic solver counterexample withheld: query depends on the unmodeled return \
             of same-crate `main::min2` (`_0`)"
                .into(),
        );
        transport.proof_evidence.as_mut().expect("proof evidence").status =
            trust_types::TransportProofStatus::Failed;

        let result = transport_to_verification_result("crate::lower", &transport, None, None);
        assert_eq!(result.outcome, VerificationOutcome::Unknown);
        assert!(
            result.reason.as_deref().is_some_and(|reason| reason.contains("withheld")),
            "{:?}",
            result.reason
        );

        // A refutation the compiler DID report keeps its verdict.
        transport.outcome = trust_types::Outcome::Failed;
        let result = transport_to_verification_result("crate::lower", &transport, None, None);
        assert_eq!(result.outcome, VerificationOutcome::Failed);
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
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: Some("obl-cache".into()),
            claim_digest_sha256: None,
            kind: "postcondition".into(),
            original_vc_snapshot: None,
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
            grade: None,
        };
        let result =
            transport_to_verification_result("crate::cached_contract", &transport, None, None);
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

    /// Every published proved row, on both lanes the producer promotes (a
    /// routed trust-mc solver proof and a Clean-kernel certificate), drops the
    /// transport envelope's duplicate `proof_evidence` copy and nothing else —
    /// and a saved copy of that report is judged exactly as one that still
    /// carries the duplicate.
    #[test]
    fn original_vc_snapshot_survives_transport_without_restoring_saved_authority() {
        let mut raw = clean_cic_hardened_transport();
        let vc = trust_types::VerificationCondition {
            function: "fixture::original".into(),
            kind: VcKind::Assertion { message: "snapshot".into() },
            location: trust_types::SourceSpan::default(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let target = "aarch64-apple-darwin;ptr64";
        let digest = trust_types::original_vc_snapshot::exact_vc_claim_digest_sha256(
            &vc,
            true,
            Some(target),
        )
        .unwrap();
        let snapshot = trust_types::OriginalVcSnapshot::capture(
            &vc,
            true,
            target,
            raw.obligation_id.as_deref().unwrap(),
            &digest,
        )
        .unwrap();
        raw.claim_digest_sha256 = Some(digest);
        raw.original_vc_snapshot = Some(Box::new(snapshot.clone()));
        let result = transport_to_verification_result("fixture::original", &raw, None, None);
        assert_eq!(
            structured_transport_evidence(&result).unwrap().original_vc_snapshot.as_deref(),
            Some(&snapshot)
        );
        let mut live =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let published = live.to_trust_report();
        let row = &published.functions[0].obligations[0];
        assert_eq!(
            row.transport_evidence.as_ref().unwrap().original_vc_snapshot.as_deref(),
            Some(&snapshot)
        );
        assert_eq!(
            row.proof_evidence.as_ref().unwrap().artifacts.len(),
            1,
            "the sidecar is not a second CIC artifact"
        );
        assert!(matches!(row.outcome, ObligationOutcome::Proved { .. }));
        let saved = serde_json::to_vec(&published).unwrap();
        let (decoded, _, _) =
            trust_types::JsonProofReport::decode_saved_json(&saved, None).unwrap();
        assert_eq!(decoded.summary.total_proved, 0, "snapshot never restores saved authority");
        assert_eq!(
            decoded.functions[0].obligations[0]
                .transport_evidence
                .as_ref()
                .unwrap()
                .original_vc_snapshot
                .as_deref(),
            Some(&snapshot)
        );
        let mut changed = structured_transport_evidence(&live.results[0]).unwrap();
        changed.original_vc_snapshot.as_mut().unwrap().original_vc_json.push(' ');
        crate::types::replace_structured_transport_evidence(&mut live.results[0], &changed)
            .unwrap();
        assert_eq!(
            live.to_trust_report().summary.total_proved,
            0,
            "new field is bound by the existing live row receipt"
        );
    }

    #[test]
    fn published_proved_rows_elide_the_duplicate_transport_proof_copy() {
        for (label, result) in [
            ("routed solver", native_full_verifier_transport_result()),
            ("clean kernel", clean_cic_hardened_result()),
        ] {
            let raw = structured_transport_evidence(&result).expect("structured transport");
            let raw_proof = raw.proof_evidence.clone().expect("raw transport proof");
            let report = with_live_transport_authority(report_with_result(
                result,
                VerificationOutcome::Proved,
            ));
            let canonical = report.to_trust_report();
            let obligation = &canonical.functions[0].obligations[0];
            assert!(matches!(obligation.outcome, ObligationOutcome::Proved { .. }), "{label}");
            let proof = obligation.proof_evidence.as_ref().expect("published proof");
            let transport = obligation.transport_evidence.as_ref().expect("transport envelope");
            assert!(transport.proof_evidence.is_none(), "{label}: duplicate copy must be elided");

            // The rest of the envelope is exactly what the raw transport carried.
            assert_eq!(transport.obligation_id, raw.obligation_id, "{label}");
            assert_eq!(transport.claim_digest_sha256, raw.claim_digest_sha256, "{label}");
            assert_eq!(transport.original_vc_snapshot, raw.original_vc_snapshot, "{label}");
            assert_eq!(transport.typed_kind, raw.typed_kind, "{label}");
            assert_eq!(transport.native_trust_ir, raw.native_trust_ir, "{label}");
            assert_eq!(transport.monitor, raw.monitor, "{label}");
            // And the published copy still says everything the dropped copy said.
            assert_eq!(proof.suite.as_deref(), Some(raw_proof.suite.as_str()), "{label}");
            assert_eq!(proof.backend, raw_proof.backend, "{label}");
            assert_eq!(proof.request_id, raw_proof.request_id, "{label}");
            assert_eq!(proof.proof_id, raw_proof.proof_id, "{label}");
            assert_eq!(proof.native_id, raw_proof.native_id, "{label}");
            assert_eq!(proof.status, Some(raw_proof.status), "{label}");
            assert_eq!(Some(&proof.strength), raw_proof.strength.as_ref(), "{label}");
            assert_eq!(Some(&proof.evidence), raw_proof.evidence.as_ref(), "{label}");
            assert_eq!(proof.artifacts, raw_proof.artifacts, "{label}");
            assert_eq!(proof.diagnostics, raw_proof.diagnostics, "{label}");

            // Saved-report decode: the elided row and the same row with the copy
            // put back are judged identically (and cleanly), and the JSON
            // carries the envelope without a `proof_evidence` member.
            let mut with_copy = obligation.clone();
            with_copy.transport_evidence.as_mut().expect("envelope").proof_evidence =
                Some(raw_proof.clone());
            assert_eq!(
                trust_types::saved_obligation_structural_proof_defect(obligation, None),
                trust_types::saved_obligation_structural_proof_defect(&with_copy, None),
                "{label}"
            );
            assert_eq!(
                trust_types::saved_obligation_structural_proof_defect(obligation, None),
                None,
                "{label}"
            );
            let json = serde_json::to_value(&canonical).expect("serialize canonical report");
            let row = &json["functions"][0]["obligations"][0];
            assert!(row["transport_evidence"].get("proof_evidence").is_none(), "{label}: {row}");
            assert!(row.get("proof_evidence").is_some(), "{label}");

            // Loading a saved report re-gates every proved row to Unknown (no
            // live replay authority). The elided report and the same report
            // with the copy put back land on the same row outcome and reason —
            // and that reason names no structural defect.
            let mut canonical_with_copy = canonical.clone();
            canonical_with_copy.functions[0].obligations[0]
                .transport_evidence
                .as_mut()
                .expect("envelope")
                .proof_evidence = Some(raw_proof.clone());
            let json_with_copy =
                serde_json::to_value(&canonical_with_copy).expect("serialize two-copy report");
            let restored: trust_types::JsonProofReport =
                serde_json::from_value(json).expect("decode canonical report");
            let restored_with_copy: trust_types::JsonProofReport =
                serde_json::from_value(json_with_copy).expect("decode two-copy report");
            let restored_row = &restored.functions[0].obligations[0];
            assert_eq!(
                trust_types::saved_obligation_structural_proof_defect(restored_row, None),
                None,
                "{label}"
            );
            match &restored_row.outcome {
                ObligationOutcome::Unknown { reason } => {
                    assert!(!reason.contains("defect"), "{label}: {reason}");
                }
                other => panic!("{label}: a saved proved row loads as Unknown, got {other:?}"),
            }
            assert_eq!(
                serde_json::to_value(&restored_row.outcome).expect("outcome"),
                serde_json::to_value(&restored_with_copy.functions[0].obligations[0].outcome)
                    .expect("outcome"),
                "{label}"
            );
            assert_eq!(
                serde_json::to_value(&restored.summary).expect("summary"),
                serde_json::to_value(&restored_with_copy.summary).expect("summary"),
                "{label}"
            );
        }
    }

    /// The elision edits the canonical projection only. The raw compiler rows
    /// — what every row receipt and the complete-report receipt hash — are
    /// byte-identical before and after, and still carry the transport proof the
    /// projection dropped.
    #[test]
    fn eliding_the_transport_proof_copy_never_touches_the_raw_rows_or_their_receipts() {
        let report = with_live_transport_authority(report_with_result(
            native_full_verifier_transport_result(),
            VerificationOutcome::Proved,
        ));
        let rows = |report: &VerificationReport| {
            report
                .results
                .iter()
                .map(|result| serde_json::to_vec(result).expect("serialize raw row"))
                .collect::<Vec<_>>()
        };
        let receipts = |report: &VerificationReport| {
            report
                .results
                .iter()
                .enumerate()
                .map(|(index, result)| {
                    live_transport_row_receipt("test-report", "session", index, result)
                })
                .collect::<Vec<_>>()
        };
        let rows_before = rows(&report);
        let receipts_before = receipts(&report);

        let canonical = report.to_trust_report();
        let obligation = &canonical.functions[0].obligations[0];
        assert!(obligation.proof_evidence.is_some());
        assert!(
            obligation
                .transport_evidence
                .as_ref()
                .is_some_and(|transport| transport.proof_evidence.is_none())
        );

        assert_eq!(rows(&report), rows_before);
        assert_eq!(receipts(&report), receipts_before);
        assert!(
            structured_transport_evidence(&report.results[0])
                .and_then(|structured| structured.proof_evidence)
                .is_some(),
            "the raw row keeps its transport proof; only the projection dropped the duplicate"
        );
    }

    /// The saving is exactly the one duplicate member, `,"proof_evidence":<copy>`
    /// inside the envelope: splicing it back into the elided bytes reproduces
    /// the report a pre-elision producer wrote, byte for byte.
    #[test]
    fn eliding_the_transport_proof_copy_shrinks_the_canonical_report_by_exactly_that_copy() {
        let result = native_full_verifier_transport_result();
        let raw_proof = structured_transport_evidence(&result)
            .and_then(|structured| structured.proof_evidence)
            .expect("raw transport proof");
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let canonical = report.to_trust_report();
        let elided_bytes = serialize_canonical_report_bounded(&canonical).expect("elided bytes");

        let mut with_copy = canonical.clone();
        with_copy.functions[0].obligations[0]
            .transport_evidence
            .as_mut()
            .expect("envelope")
            .proof_evidence = Some(raw_proof.clone());
        let full_bytes = serialize_canonical_report_bounded(&with_copy).expect("full bytes");

        let member = [
            b",\"proof_evidence\":".as_slice(),
            &serde_json::to_vec(&raw_proof).expect("serialize transport copy"),
        ]
        .concat();
        let occurrences = full_bytes
            .windows(member.len())
            .enumerate()
            .filter(|(_, window)| *window == member.as_slice())
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        assert_eq!(occurrences.len(), 1, "the transport copy is one member of the envelope");
        let start = occurrences[0];
        let spliced = [&full_bytes[..start], &full_bytes[start + member.len()..]].concat();
        assert_eq!(spliced, elided_bytes);
        assert_eq!(full_bytes.len() - elided_bytes.len(), member.len());
    }

    /// A row the producer did not promote has no obligation copy, so its
    /// transport record is the only account of what the transport claimed. It
    /// is kept.
    #[test]
    fn unpromoted_rows_keep_their_transport_proof_record() {
        let mut transport = native_full_verifier_transport();
        transport.native_trust_ir = None;
        if let Some(proof) = transport.proof_evidence.as_mut() {
            proof.strength = None;
            proof.evidence = None;
            proof.artifacts.clear();
        }
        let result =
            transport_to_verification_result("crate::checked_contract", &transport, None, None);
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let canonical = report.to_trust_report();
        let obligation = &canonical.functions[0].obligations[0];

        assert!(obligation.proof_evidence.is_none());
        let envelope = obligation.transport_evidence.as_ref().expect("transport envelope");
        assert!(envelope.proof_evidence.is_some(), "an unpromoted row keeps its transport record");
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
        let result =
            transport_to_verification_result("crate::checked_contract", &transport, None, None);
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
        let second = transport_to_verification_result(
            "crate::second_contract",
            &second_transport,
            None,
            None,
        );
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
        config.config.budget_profile.backstop.per_mille += 1;
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
        let result =
            transport_to_verification_result("crate::checked_contract", &transport, None, None);
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
            let result =
                transport_to_verification_result("crate::checked_contract", &transport, None, None);
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
        for suite in ["trust-mc", "trust-vc"] {
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
        for suite in ["trust-mc", "trust-vc"] {
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
        for suite in ["trust-mc", "trust-vc"] {
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
    fn historical_trust_wp_transport_is_never_publication_grade() {
        let transport = native_transport_for_suite("trust-wp");
        assert_eq!(transport.outcome, trust_types::Outcome::Proved);
        assert!(transport.native_trust_ir.as_ref().is_some_and(|native| native.present));
        assert!(transport.proof_evidence.is_some());
        assert!(
            promoted_proof_evidence_for_transport(transport).is_none(),
            "a structurally valid historical TrustWP row must remain decodable without reviving publication authority"
        );
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

    fn determinism_row(
        function: &str,
        outcome: VerificationOutcome,
        reason: Option<String>,
    ) -> VerificationResult {
        with_stable_key(
            VerificationResult {
                function: function.to_string(),
                kind: "overflow:add".to_string(),
                message: "arithmetic overflow (Add)".to_string(),
                outcome,
                backend: "ay-in-process".to_string(),
                time_ms: Some(1),
                location: None,
                counterexample: None,
                reason,
                raw_line: String::new(),
            },
            0,
        )
    }

    /// Determinism plan §3.6/§3.7: the header names the budget profile, the
    /// Summary keeps its counts and appends outcome, profile and vector, and a
    /// stop-cause line follows.
    #[test]
    fn terminal_lines_print_the_budget_profile_and_the_determinism_suffix() {
        use trust_types::determinism::{StopCause, short_id};
        let report = report_with_results_and_diagnostics(
            vec![
                determinism_row("m::f", VerificationOutcome::Proved, None),
                determinism_row(
                    "m::g",
                    VerificationOutcome::Unknown,
                    Some(StopCause::Effort.stamp("ay unknown (resourceout; 100000 conflicts)")),
                ),
            ],
            vec![],
        );
        let rendered = report.terminal_lines().join("\n");
        assert!(rendered.contains(&report.config.budget_profile.header_line()), "{rendered}");
        let determinism = report.determinism();
        let summary = rendered
            .lines()
            .find(|line| line.starts_with("Summary: "))
            .unwrap_or_else(|| panic!("a measured run prints its Summary:\n{rendered}"));
        assert!(summary.contains("(2 total); measured; profile "), "{summary}");
        assert!(
            summary.ends_with(&format!(
                "profile {}; vector {}",
                short_id(&report.config.budget_profile.id()),
                short_id(&determinism.vector.digest())
            )),
            "{summary}"
        );
        assert!(rendered.contains("Stop causes: effort=1 solved=1"), "{rendered}");
    }

    /// DECISION_QUEUE "Project policy cannot loosen the lane — 2026-10-07": a
    /// lane adopted from Cargo project configuration is named in the report
    /// header and in the serialized report; without one, neither mentions it.
    #[test]
    fn report_publishes_adopted_project_requirements_in_every_artifact() {
        let requirements = trust_types::ProjectRequirementsReport {
            policy: Some("advisory".into()),
            level: Some("L1".into()),
            profile: None,
            include_dependencies: None,
            ir_lower: None,
            verification_required: false,
        };
        let published = |requirements: Option<trust_types::ProjectRequirementsReport>| {
            let mut report = report_with_results_and_diagnostics(
                vec![determinism_row("m::f", VerificationOutcome::Proved, None)],
                vec![],
            );
            report.config.project_requirements = requirements;
            report.install_gate(failed_gate(0, 1));
            let terminal = report.terminal_lines().join("\n");
            let trust_report = report.to_trust_report();
            let json = serde_json::to_value(&trust_report).expect("published report serializes");
            let html = trust_report::html_report::generate_html_report(&trust_report);
            let output_dir = tempfile::tempdir().expect("tempdir");
            write_report_artifacts(&trust_report, output_dir.path(), &html)
                .expect("report artifacts should be written");
            let saved: serde_json::Value = serde_json::from_slice(
                &fs::read(output_dir.path().join("report.json")).expect("read report.json"),
            )
            .expect("report.json parses");
            let ndjson =
                fs::read_to_string(output_dir.path().join("report.ndjson")).expect("read ndjson");
            (terminal, json, saved, ndjson, html)
        };

        let (terminal, json, saved, ndjson, html) = published(None);
        assert!(!terminal.contains("Project requirements:"), "{terminal}");
        assert!(json["verification_gate"].get("project_requirements").is_none(), "{json}");
        assert!(saved["verification_gate"].get("project_requirements").is_none(), "{saved}");
        assert!(!ndjson.contains("project_requirements"), "{ndjson}");
        assert!(!html.contains("Project requirements"), "{html}");

        let (terminal, json, saved, ndjson, html) = published(Some(requirements));
        let header_end = terminal.find("\n\n  ").unwrap_or(terminal.len());
        assert!(
            terminal[..header_end].contains(
                "Project requirements: policy=advisory, level=L1 (Cargo project configuration; adopted for this run)"
            ),
            "{terminal}"
        );
        let expected = serde_json::json!({"policy": "advisory", "level": "L1", "verification_required": false});
        assert_eq!(json["verification_gate"]["project_requirements"], expected, "{json}");
        assert_eq!(saved["verification_gate"]["project_requirements"], expected, "{saved}");
        assert!(
            html.contains(
                "<strong class=\"project-requirements\">policy=advisory, level=L1</strong>"
            ),
            "{html}"
        );
        assert!(
            ndjson.contains(r#""project_requirements":{"policy":"advisory","level":"L1""#),
            "{ndjson}"
        );
    }

    /// Verified-lane blockers issue, item 4: a run whose report artifacts cannot
    /// be written (e.g. past the artifact-store cap) still shows its counts, but
    /// framed as NOT PUBLISHED, and never with the run's own `Result:` line.
    #[test]
    fn an_unsaved_report_keeps_its_counts_and_never_prints_a_result() {
        let report = report_with_results_and_diagnostics(
            vec![determinism_row("m::f", VerificationOutcome::Proved, None)],
            vec![],
        );
        let published = report.terminal_lines().join("\n");
        assert!(published.lines().any(|line| line.starts_with("Result: ")), "{published}");

        let error = io::Error::new(io::ErrorKind::InvalidData, "store exceeds the cap");
        let lines = report.unpublished_terminal_lines(&error);
        let rendered = lines.join("\n");
        assert!(rendered.contains("=== REPORT NOT SAVED: store exceeds the cap ==="), "{rendered}");
        assert!(rendered.lines().any(|line| line.starts_with("Summary: ")), "{rendered}");
        let results: Vec<&String> =
            lines.iter().filter(|line| line.starts_with("Result: ")).collect();
        assert_eq!(
            results,
            [&"Result: NOT PUBLISHED (report artifact evidence gate failed: store exceeds the cap)"
                .to_string()],
            "exactly one Result line, and it is the not-published one"
        );
    }

    /// Merge of blocker 4 with 80d00f02b0: a run that SAVED its report but
    /// exits 2 because it requires a complete evidence bundle and got an
    /// incomplete one keeps every measured line, but its `Result:` is replaced
    /// in place and its sealed `Gate:` line is relabelled as overridden, so no
    /// pass is printed beside that exit.
    #[test]
    fn an_evidence_gate_failure_keeps_its_counts_and_never_prints_a_pass() {
        let report = report_with_results_and_diagnostics(
            vec![determinism_row("m::f", VerificationOutcome::Proved, None)],
            vec![],
        );
        let published = report.terminal_lines();
        let lines = report.evidence_gate_failed_terminal_lines();
        assert_eq!(lines.len(), published.len(), "only the Result line is replaced");
        let rendered = lines.join("\n");
        assert!(rendered.lines().any(|line| line.starts_with("Summary: ")), "{rendered}");
        let results: Vec<&String> =
            lines.iter().filter(|line| line.starts_with("Result: ")).collect();
        assert_eq!(results, [&EVIDENCE_GATE_FAILED_RESULT.to_string()]);

        let summary = "Verification summary\n  Gate: PASS [strict lane, exit 0] (1 proved, 0 failed / 1 total)\n  tail";
        let relabelled = summary_with_overridden_gate(summary);
        assert!(
            !relabelled.lines().any(|line| line.trim_start().starts_with("Gate: ")),
            "{relabelled}"
        );
        assert!(
            relabelled.contains(
                "  Sealed gate (OVERRIDDEN: this run exits 2 on the report artifact evidence gate): PASS [strict lane, exit 0] (1 proved, 0 failed / 1 total)"
            ),
            "{relabelled}"
        );
        assert!(
            relabelled.starts_with("Verification summary\n") && relabelled.ends_with("\n  tail")
        );
    }

    #[test]
    fn an_unexplained_stop_flags_the_summary_not_reproducible() {
        let report = report_with_results_and_diagnostics(
            vec![determinism_row(
                "m::f",
                VerificationOutcome::Unknown,
                Some("solver returned unknown".into()),
            )],
            vec![],
        );
        let rendered = report.terminal_lines().join("\n");
        assert!(rendered.contains("(1 total); not-reproducible; profile "), "{rendered}");
        assert!(rendered.contains("unclassified=1"), "{rendered}");
        assert!(rendered.contains("NOT REPRODUCIBLE"), "{rendered}");
    }

    /// Plan §2: an admission refusal is COULD NOT RUN, never an Unknown in a
    /// count — so no `Summary:` line is printed at all.
    #[test]
    fn an_admission_refusal_prints_no_summary() {
        use trust_types::determinism::StopCause;
        let report =
            report_with_results_and_diagnostics(
                vec![
                    determinism_row("m::f", VerificationOutcome::Proved, None),
                    determinism_row(
                        "m::g",
                        VerificationOutcome::Unknown,
                        Some(StopCause::AdmissionRefused.stamp(
                            "memory admission failed before solver spawn: trustd unreachable",
                        )),
                    ),
                ],
                vec![],
            );
        let rendered = report.terminal_lines().join("\n");
        assert!(
            !rendered.lines().any(|line| line.trim_start().starts_with("Summary:")),
            "a run that could not run has no Summary:\n{rendered}"
        );
        assert!(
            rendered.contains(
                "COULD NOT RUN: verification did not run to a measurement: 1 obligation(s)"
            ),
            "{rendered}"
        );
    }

    #[test]
    fn record_determinism_puts_the_block_on_the_gate() {
        use trust_types::determinism::UnitOutcome;
        let mut report = report_with_results_and_diagnostics(
            vec![determinism_row("m::f", VerificationOutcome::Proved, None)],
            vec![],
        );
        report.gate = Some(trust_types::VerificationGateReport {
            lane: "default".into(),
            verification_level: Some("L1".into()),
            decision: "pass".into(),
            exit_code: 0,
            counts: trust_types::VerificationGateCounts {
                total: 1,
                proved: 1,
                failed: 0,
                unknown: 0,
                runtime_checked: 0,
                assumed: 0,
                mandated: 0,
                contract_panics: 0,
                excluded: 0,
            },
            conditional_on_assumption_rows: false,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: false,
            conditional_on_unknown_rows: false,
            conditional_on_visitation_entries: false,
            coverage: None,
            test_execution: None,
            exclusions: Vec::new(),
            determinism: None,
            failure_sites: None,
            project_requirements: None,
        });
        report.record_determinism();
        let block = report.gate.as_ref().and_then(|gate| gate.determinism.as_ref()).unwrap();
        assert_eq!(block.outcome, UnitOutcome::Measured);
        assert_eq!(block.vector_digest, report.determinism().vector.digest());
        assert_eq!(block.budget_profile_id, report.config.budget_profile.id());
        assert_eq!(block.vector.len(), 1);
        let json = serde_json::to_string(report.gate.as_ref().unwrap()).unwrap();
        assert!(json.contains("\"determinism\":{\"outcome\":\"measured\""), "{json}");
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
            "Certified test execution: schema=trust.certified-test-execution.v3 completion_scope=top-level-cargo-child-exit-only-v1 state=cargo-invocation-exited requested=true compile_only=false phase_a_exit=0 phase_a_success=true authorized_executables=1 phase_b_exit=101"
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
            "Certified test execution: schema=trust.certified-test-execution.v3 completion_scope=top-level-cargo-child-exit-only-v1 state=blocked requested=true compile_only=false phase_a_exit=2 phase_a_success=false blocker=\"phase A failed\\nbefore execution\""
        );

        let mut retained = completed;
        retained.completion_scope =
            CertifiedTestExecutionCompletionScope::RetainedCompileCheckpointAndChildExitV1;
        retained.scope = trust_types::CERTIFIED_RETAINED_TEST_EXECUTION_SCOPE.into();
        let line = certified_test_execution_terminal_line(&retained);
        assert!(line.contains("phase_a_compile_checkpoint_status=0"), "{line}");
        assert!(!line.contains("phase_a_exit="), "a live checkpoint is not an exit: {line}");
        assert!(line.contains("phase_b_exit=101"), "{line}");
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

        // Dropped (2026-10-17): the compiler EMITTED a row and an advisory lane
        // dropped it for a defect. That is not an absent row and must not read as
        // one: the line names the defect (aterm-serde's identity defect read
        // "older toolchain?" on the 2026-10-16 candidate gate).
        let mut dropped = report_with_full_verifier_result(VerificationOutcome::Proved);
        dropped.coverage_dropped = vec![
            "aterm-serde (lib): Trust coverage function identity authentication failed: \
             processed coverage identities did not exactly equal authenticated function envelopes"
                .to_string(),
            "second".to_string(),
        ];
        let rendered = dropped.terminal_lines().join("\n");
        assert!(
            rendered.contains(
                "Coverage: unknown (the compiler emitted a coverage_summary transport row and \
                 targo dropped it: aterm-serde (lib): Trust coverage function identity \
                 authentication failed"
            ),
            "a dropped row must be reported as dropped, naming the defect: {rendered}"
        );
        assert!(rendered.contains("; and 1 more)"), "{rendered}");
        assert!(!rendered.contains("older toolchain"), "{rendered}");
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
    fn hardened_context_links_structured_model_assumptions_and_proof_evidence() {
        let report = report_with_results_and_diagnostics(
            vec![hardened_transport_result_with_context()],
            Vec::new(),
        );

        // The existing bound-artifact fixture is a report control, not a real
        // proof. Its serialized evidence cannot authorize publication by itself.
        let untrusted = report.to_trust_report();
        assert_eq!(untrusted.summary.total_proved, 0);
        assert!(untrusted.functions[0].obligations[0].proof_evidence.is_none());

        // Reuse the same test-only authenticated-publication setup as the
        // neighboring native-evidence gate controls; change no artifact bytes.
        let report = with_live_transport_authority(report);
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
            Some("trust_ir-native-trust-mc-request-8-proof-9")
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
        assert_eq!(proof.proof_evidence_id.as_deref(), Some("9"));
        assert_eq!(proof.proof_evidence_id, evidence.proof_id);
        assert_eq!(proof.source.as_deref(), Some("trust-mc"));
        assert_eq!(proof.source.as_deref(), Some(evidence.backend.as_str()));
        assert_eq!(proof.obligation_id, obligation.obligation_id);

        let saved = serde_json::to_vec(&trust_report).expect("serialize report fixture");
        let (decoded, sanitization, _) =
            trust_types::JsonProofReport::decode_saved_json(&saved, None)
                .expect("decode saved report");
        assert_eq!(sanitization.downgraded_proved, 1);
        assert_eq!(decoded.summary.total_proved, 0, "saved evidence cannot restore live authority");
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

    // ---- Trust (#220): publication normalization and its separate diagnostics.

    fn publication_probe_span() -> SourceSpan {
        SourceSpan {
            file: "src/probe.rs".into(),
            line_start: 41,
            col_start: 9,
            line_end: 41,
            col_end: 20,
        }
    }

    /// A per-statement bounds VC that PUBLISHES: it carries the content-addressed
    /// clean-CIC kernel artifact `authenticated_proved_row_has_publication_evidence`
    /// demands, so publication normalization leaves it `Proved`.
    fn publishing_bounds_sibling() -> VerificationResult {
        let mut transport = clean_cic_hardened_transport();
        transport.obligation_id = Some("vc:crate::probe:bounds_check:0".into());
        transport.kind = "bounds".into();
        transport.description = "slice bounds check".into();
        transport.location = Some(publication_probe_span());
        transport_to_verification_result("crate::probe", &transport, None, None)
    }

    /// The hardened `mir_assert::BoundsCheck` twin at the SAME span. The compiler
    /// reported it `Proved` (an `ay-in-process` decision), but it carries no
    /// kernel or native evidence, so publication demotes it.
    fn evidence_free_bounds_twin(outcome: trust_types::Outcome) -> VerificationResult {
        let transport = trust_types::TransportObligationResult {
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: Some("vc:crate::probe:panic_boundary:0".into()),
            claim_digest_sha256: Some("d".repeat(64)),
            kind: "hardened_panic_boundary".into(),
            original_vc_snapshot: None,
            typed_kind: None,
            description: "hardened boundary (panic_boundary): mir_assert::BoundsCheck: MIR \
                          bounds assert can panic"
                .into(),
            location: Some(publication_probe_span()),
            outcome,
            solver: "ay-in-process".into(),
            time_ms: 2,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            native_trust_ir: None,
            proof_evidence: None,
            monitor: None,
            grade: None,
        };
        transport_to_verification_result("crate::probe", &transport, None, None)
    }

    /// THE CRUX of #220. A favorable compiler row has two possible fates at the
    /// publication boundary, and they are not equally visible:
    ///
    ///   * relabelled — stays in the vector as `Unknown` carrying the verbatim
    ///     demotion reason, which `--json` shows and a reader can grep;
    ///   * DELETED — demotion runs before `elide_rows_proved_only_by`, so a
    ///     demoted hardened twin whose direct sibling published is removed
    ///     from the proof vector. The separate boundary diagnostic now retains
    ///     its identity and reason without restoring proof credit.
    ///
    /// Counting the demotion marker therefore UNDER-reports, and an
    /// under-reporting disclosure is worse than none because it reads as
    /// complete. This test pins the second fate: it asserts the row is gone AND
    /// that the boundary record preserves its diagnostic fate.
    #[test]
    fn a_demoted_hardened_twin_is_deleted_outright_when_its_sibling_publishes() {
        let mut results = vec![
            publishing_bounds_sibling(),
            evidence_free_bounds_twin(trust_types::Outcome::Proved),
        ];
        assert!(
            results.iter().all(|result| result.outcome.is_proved()),
            "premise: BOTH rows leave the compiler with a favorable outcome"
        );

        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut results, None);

        assert_eq!(results.len(), 1, "the hardened twin must be gone, not merely relabelled");
        assert_eq!(results[0].kind, "bounds");
        assert!(results[0].outcome.is_proved(), "the kernel-certified sibling publishes");
        assert!(
            !results.iter().any(|result| result
                .reason
                .as_deref()
                .is_some_and(|reason| reason.contains("downgraded before publication"))),
            "the deleted proof row leaves no demotion reason in the proof vector — counting \
             that vector's marker text under-reports"
        );

        assert_eq!(boundary.compiler_favorable, 2);
        assert_eq!(boundary.published_favorable, 1);
        assert_eq!(boundary.withheld(), 1);
        assert_eq!(
            boundary.withheld_elided, 1,
            "the withheld row must be attributed to the DELETED fate"
        );
        assert_eq!(boundary.withheld_relabelled, 0);
        assert_eq!(boundary.alias_elided, 0);
        assert_eq!(boundary.elided_diagnostics.len(), 1);
        assert!(boundary.elided_diagnostics[0].withheld);
        assert_eq!(boundary.unattributed_withheld(), 0);
    }

    /// Controls for the test above, each isolating one premise of the deletion.
    #[test]
    fn a_demoted_hardened_twin_stays_visible_when_its_sibling_does_not_publish() {
        // Same pair, except the direct sibling carries no publishable evidence
        // either. It is demoted too, so it cannot subsume, so nothing is deleted
        // and BOTH withheld rows are recoverable from the published vector.
        let mut sibling = publishing_bounds_sibling();
        let mut evidence =
            crate::types::structured_transport_evidence(&sibling).expect("structured row");
        evidence.proof_evidence = None;
        crate::types::replace_structured_transport_evidence(&mut sibling, &evidence)
            .expect("re-encode structured evidence");

        let mut results = vec![sibling, evidence_free_bounds_twin(trust_types::Outcome::Proved)];
        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut results, None);

        assert_eq!(results.len(), 2, "with no publishing sibling, nothing is elided");
        assert_eq!(boundary.compiler_favorable, 2);
        assert_eq!(boundary.published_favorable, 0);
        assert_eq!(boundary.withheld(), 2);
        assert_eq!(boundary.withheld_relabelled, 2);
        assert_eq!(boundary.withheld_elided, 0);
        assert_eq!(boundary.unattributed_withheld(), 0);
    }

    /// A twin the COMPILER already reported `Unknown` is elided by the same
    /// retain predicate, but it is not a withheld proof — it is the pass's
    /// pre-existing redundant-alias removal. Keeping the two apart is what makes
    /// the disclosed split meaningful rather than a restatement of `results.len()`.
    #[test]
    fn an_unknown_twin_elided_as_an_alias_is_not_counted_as_withheld() {
        let mut results = vec![
            publishing_bounds_sibling(),
            evidence_free_bounds_twin(trust_types::Outcome::Unknown),
        ];
        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut results, None);

        assert_eq!(results.len(), 1);
        assert_eq!(boundary.compiler_favorable, 1);
        assert_eq!(boundary.published_favorable, 1);
        assert_eq!(boundary.withheld(), 0);
        assert_eq!(boundary.withheld_elided, 0);
        assert_eq!(boundary.alias_elided, 1);
        assert_eq!(boundary.elided_diagnostics.len(), 1);
        assert_eq!(boundary.elided_diagnostics[0].outcome, VerificationOutcome::Unknown);
        assert!(!boundary.elided_diagnostics[0].withheld);
    }

    #[test]
    fn omitted_unknown_request_retains_identity_and_action_without_changing_gate() {
        let mut twin = evidence_free_bounds_twin(trust_types::Outcome::Unknown);
        twin.reason = Some("PDR invariant candidate requires exact consumer replay".into());
        let mut evidence = structured_transport_evidence(&twin).expect("structured twin");
        evidence.native_trust_ir = Some(trust_types::TransportNativeTrustIrEvidence {
            suite: "trust-mc".into(),
            backend: "typed-chc-pdr".into(),
            request_id: Some("17".into()),
            native_id: Some("trust-ir-request-17".into()),
            present: true,
            artifacts: Vec::new(),
            diagnostics: Vec::new(),
        });
        crate::types::replace_structured_transport_evidence(&mut twin, &evidence)
            .expect("replace diagnostic transport");
        let mut rows = vec![publishing_bounds_sibling(), twin];
        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
        assert_eq!(rows.len(), 1, "normalization must remain unchanged");
        assert_eq!(boundary.withheld(), 0, "compiler Unknown is not a withheld proof");

        let mut report = report_with_results_and_diagnostics(rows, Vec::new());
        report.success = false;
        report.exit_code = 1;
        let before = serde_json::to_vec(&report).expect("report before disclosure");
        report.publication_boundary = Some(boundary);
        assert_eq!(
            serde_json::to_vec(&report).unwrap(),
            before,
            "diagnostic disclosure cannot change serialized proof inputs"
        );
        let lines = report.terminal_lines().join("\n");
        for expected in [
            "Compiler requests omitted from the published proof rows: 1",
            "[UNKNOWN] function=crate::probe",
            "obligation=vc:crate::probe:panic_boundary:0",
            "kind=hardened_panic_boundary",
            "mir_assert::BoundsCheck",
            "@ src/probe.rs:41:9",
            "suite=trust-mc request_id=17 native_id=trust-ir-request-17",
            "PDR invariant candidate requires exact consumer replay",
            "Next: resolve or replay evidence for the exact request",
            "compiler refusal and final gate remain unchanged",
        ] {
            assert!(lines.contains(expected), "missing {expected:?}:\n{lines}");
        }
        assert!(lines.contains(&format!("claim_sha256={}", "d".repeat(64))));
        assert!(!report.success);
        assert_eq!(report.exit_code, 1);
        assert_eq!(report.total, 1);
        assert_eq!(report.proved, 1);
        assert_eq!(report.unknown, 0);
        assert_eq!(
            report.to_trust_report().summary.verdict,
            trust_types::CrateVerdict::Inconclusive
        );
    }

    #[test]
    fn elided_demotion_is_disclosed_without_inventing_request_identity() {
        let mut rows = vec![
            publishing_bounds_sibling(),
            evidence_free_bounds_twin(trust_types::Outcome::Proved),
        ];
        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut rows, None);
        let mut report = report_with_results_and_diagnostics(rows, Vec::new());
        report.publication_boundary = Some(boundary);
        let lines = report.elided_publication_diagnostic_lines().join("\n");
        assert!(lines.contains("[UNKNOWN; proof withheld at publication]"));
        assert!(lines.contains("downgraded before publication"));
        assert!(lines.contains("request_id=unavailable native_id=unavailable"));
        assert!(lines.contains("diagnostics only; not discharged by this report"));
    }

    /// Conservation. `compiler_favorable` must equal the published favorable rows
    /// plus BOTH withheld fates, over a vector that exercises every branch at
    /// once: a publishing row, a demoted-and-deleted row, a demoted-but-visible
    /// row, and a zero-obligation inventory row (which is inventory, not an
    /// obligation, and must not enter the withheld arithmetic at all).
    #[test]
    fn publication_boundary_conservation_holds_across_both_fates() {
        let mut lone_demotion = evidence_free_bounds_twin(trust_types::Outcome::Proved);
        // A different function, so it has no sibling to be subsumed by and stays
        // in the vector as a relabelled Unknown.
        lone_demotion.function = "crate::other".into();

        // Trust (2026-09-16): the THIRD fate — a policy-B `RuntimeChecked`
        // relabel — must sit on the withheld side of the law, or an
        // evidence-free compiler proof claim would read as published.
        let (closure_fn, closure_row) = real_p7_closure_assert_refute_transport();
        let policy_b_relabel =
            transport_to_verification_result(&closure_fn, &closure_row, None, None);

        let mut results = vec![
            publishing_bounds_sibling(),
            evidence_free_bounds_twin(trust_types::Outcome::Proved),
            lone_demotion,
            policy_b_relabel,
            VerificationResult {
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
            },
        ];

        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut results, None);

        assert_eq!(boundary.inventory_elided, 1, "inventory is removed before any counting");
        assert_eq!(boundary.compiler_favorable, 4, "and never counted as an obligation");
        assert_eq!(boundary.published_favorable, 1);
        assert_eq!(boundary.withheld_relabelled, 2);
        assert_eq!(boundary.withheld_relabelled_runtime_checked, 1);
        assert_eq!(boundary.withheld_elided, 1);
        assert_eq!(
            results
                .iter()
                .filter(|result| result.outcome == VerificationOutcome::RuntimeChecked)
                .count(),
            1,
            "the policy-B row is still favorable in the published vector"
        );
        assert_eq!(
            boundary.compiler_favorable,
            boundary.published_favorable + boundary.withheld_relabelled + boundary.withheld_elided,
            "conservation: every favorable compiler row is published, relabelled, or deleted"
        );
        assert_eq!(boundary.unattributed_withheld(), 0);
    }

    /// Trust (2026-09-16, T4 of `reports/2026-09-13-w1-alignment-obligation-sizing.md`):
    /// measured on `trust-acb74dd5`, this row was the ONLY thing between
    /// `p7_helper_print` and CONDITIONAL-PASS under `targo trust build` — raw
    /// `trustc` proved the body (exit 0, binary ran), the publication boundary
    /// withheld the row to `Unknown`, and the strict gate graded the crate
    /// INCONCLUSIVE (exit 1, no binary). Policy B at the boundary publishes it
    /// as `runtime_checked` with the reason, counts it conditional, and still
    /// discloses it as a WITHHELD proof claim.
    #[test]
    fn real_evidence_free_interprocedural_closure_row_publishes_runtime_checked_under_policy_b() {
        let (function, transport) = real_p7_closure_assert_refute_transport();
        assert_eq!(
            transport.outcome,
            trust_types::Outcome::Proved,
            "control: the compiler said proved"
        );
        assert_eq!(transport.solver, "trust-assert-refute", "control: the closure seam");
        assert!(
            transport.proof_evidence.is_none() && transport.native_trust_ir.is_none(),
            "control: nothing attachable"
        );
        assert!(transport.claim_digest_sha256.is_some(), "control: exact claim identity");
        assert!(
            matches!(transport.typed_kind.as_deref(), Some(trust_types::VcKind::Assertion { .. })),
            "control: a typed whole-function panic-freedom row"
        );

        let result = transport_to_verification_result(&function, &transport, None, None);
        let report =
            with_live_transport_authority(report_with_result(result, VerificationOutcome::Proved));
        let boundary = report.publication_boundary.clone().expect("publication boundary");

        // The published row: runtime-checked, carrying the reason, no proof credit.
        assert_eq!(report.results.len(), 1);
        assert_eq!(report.results[0].outcome, VerificationOutcome::RuntimeChecked);
        let reason = report.results[0].reason.clone().unwrap_or_default();
        assert!(
            reason.contains("without attachable native or clean-kernel proof evidence"),
            "{reason}"
        );
        assert!(reason.contains("runtime-checked under policy B"), "{reason}");
        assert!(
            reason.contains("`trust-assert-refute`"),
            "the reason names the compiler's claim: {reason}"
        );
        // The canonical JSON report agrees with the terminal counts.
        let obligation = report.to_trust_report().functions.remove(0).obligations.remove(0);
        assert!(
            matches!(obligation.outcome, ObligationOutcome::RuntimeChecked { .. }),
            "got {:?}",
            obligation.outcome
        );
        assert!(
            obligation.proof_evidence.is_none(),
            "no proof evidence is minted for a withheld claim"
        );
        // Counts and gate: conditional, never proved; the crate builds.
        assert_eq!((report.proved, report.runtime_checked, report.unknown), (0, 1, 0));
        let gate = report.gate.as_ref().expect("gate");
        assert_eq!(gate.decision, "conditional-pass");
        assert_eq!(gate.exit_code, 0);
        assert!(gate.conditional_on_runtime_checks);
        // The boundary still discloses a WITHHELD proof claim, attributed to the
        // policy-B fate, and the conservation law holds.
        assert_eq!(boundary.compiler_favorable, 1);
        assert_eq!(
            boundary.published_favorable, 0,
            "a policy-B relabel is a withheld proof claim, not a published one"
        );
        assert_eq!(boundary.withheld(), 1);
        assert_eq!(boundary.withheld_relabelled, 1);
        assert_eq!(boundary.withheld_relabelled_runtime_checked, 1);
        assert_eq!(boundary.withheld_elided, 0);
        assert_eq!(boundary.unattributed_withheld(), 0);
        let line = report.publication_boundary_line();
        assert!(line.contains("1 WITHHELD"), "{line}");
        assert!(line.contains("0 relabelled unknown"), "{line}");
        assert!(line.contains("1 relabelled runtime-checked under policy B"), "{line}");
    }

    /// Controls for the relabel above, each isolating one premise on the SAME
    /// real row. Every one must still fail closed to `Unknown`, and none may
    /// register in the policy-B sub-count. Two cases never even reach the
    /// boundary favorable — `UnsupportedMir` and a typed kind that disagrees
    /// with its legacy tag — because `transport_to_verification_result`'s
    /// fail-closed parse rules demote them first; that earlier guard is pinned
    /// here as such.
    #[test]
    fn the_policy_b_relabel_needs_an_exact_typed_kind_whose_runtime_check_is_unconditional() {
        use trust_types::{BinOp, Ty, VcKind};
        fn retyped(
            mut transport: trust_types::TransportObligationResult,
            kind: VcKind,
        ) -> trust_types::TransportObligationResult {
            transport.kind = kind.transport_tag();
            transport.description = kind.description();
            transport.typed_kind = Some(Box::new(kind));
            transport
        }
        let (function, base) = real_p7_closure_assert_refute_transport();
        let i32_ty = Ty::Int { width: 32, signed: true };
        // (label, row, still favorable when it reaches the boundary?)
        let cases = vec![
            (
                "a precondition has no runtime fallback",
                retyped(base.clone(), VcKind::Precondition { callee: "dep::f".into() }),
                true,
            ),
            ("a postcondition has none", retyped(base.clone(), VcKind::Postcondition), true),
            (
                "the separation engine's unsafe assertions encode UB, which rustc never checks",
                retyped(
                    base.clone(),
                    VcKind::Assertion {
                        message: format!("{}double-free", VcKind::SEP_UNSAFE_ASSERTION_PREFIX),
                    },
                ),
                true,
            ),
            (
                "an overflow fallback is overflow_checks-gated, and targo does not know the \
                 unit's setting",
                retyped(
                    base.clone(),
                    VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (i32_ty.clone(), i32_ty.clone()),
                    },
                ),
                true,
            ),
            (
                "an UnsupportedMir row cannot vouch for any fallback, even one its text names",
                retyped(
                    base.clone(),
                    VcKind::UnsupportedMir {
                        kind: "assert".into(),
                        detail: "assertion: panic freedom".into(),
                    },
                ),
                false,
            ),
            (
                "no exact claim identity",
                {
                    let mut transport = base.clone();
                    transport.claim_digest_sha256 = None;
                    transport
                },
                true,
            ),
            (
                "the typed kind disagrees with the legacy tag (demoted at parse time already)",
                {
                    let mut transport = base.clone();
                    transport.kind = "bounds".into();
                    transport
                },
                false,
            ),
            (
                "an untyped row",
                {
                    let mut transport = base.clone();
                    transport.typed_kind = None;
                    transport
                },
                true,
            ),
            // Refuted 2026-09-16: the whole `[unsafe…]` family (UB/FFI claims
            // rustc never checks) and `[provenance]` used to answer `true`
            // because only `[unsafe:sep:` was carved out of the predicate.
            (
                "a raw-deref null check is UB-class, not a rustc check",
                retyped(
                    base.clone(),
                    VcKind::Assertion { message: "[unsafe:deref] null check for *p".into() },
                ),
                true,
            ),
            (
                "the generic unsafe tag",
                retyped(
                    base.clone(),
                    VcKind::Assertion { message: "[unsafe] null pointer check for: p".into() },
                ),
                true,
            ),
            (
                "an FFI boundary claim",
                retyped(
                    base.clone(),
                    VcKind::Assertion {
                        message: "[unsafe:ffi] null pointer argument check for getenv".into(),
                    },
                ),
                true,
            ),
            (
                "the separation-logic mint spells its tag without the trailing colon",
                retyped(
                    base.clone(),
                    VcKind::Assertion {
                        message: "[unsafe:sep] heap precondition for unsafe block in f".into(),
                    },
                ),
                true,
            ),
            (
                "an unmodeled call",
                retyped(
                    base.clone(),
                    VcKind::Assertion { message: "[unsafe:unmodeled-call] f".into() },
                ),
                true,
            ),
            (
                "a provenance claim",
                retyped(
                    base.clone(),
                    VcKind::Assertion { message: "[provenance] use-after-free: x".into() },
                ),
                true,
            ),
            // Refuted 2026-09-16: a `proved` label with ATTACHED evidence whose
            // status is not `proved` is a laundering attempt, and for a solver
            // name the parse-time normalizer does not re-derive it reaches the
            // boundary still favorable. Policy B is for the EVIDENCE-FREE
            // defect only.
            (
                "attached evidence with a failed status behind a proved label",
                {
                    let mut transport = base.clone();
                    transport.proof_evidence = Some(trust_types::TransportProofEvidence {
                        suite: "trust-vc".into(),
                        backend: "trust-vc".into(),
                        request_id: None,
                        proof_id: None,
                        native_id: None,
                        status: trust_types::TransportProofStatus::Failed,
                        strength: None,
                        evidence: None,
                        artifacts: Vec::new(),
                        diagnostics: Vec::new(),
                    });
                    transport
                },
                true,
            ),
        ];
        for (label, transport, favorable_at_boundary) in cases {
            let mut results =
                vec![transport_to_verification_result(&function, &transport, None, None)];
            assert_eq!(
                results[0].outcome.is_proved(),
                favorable_at_boundary,
                "{label}: premise — whether the compiler row is still favorable at the boundary"
            );
            let boundary =
                crate::types::normalize_authenticated_results_for_publication(&mut results, None);
            assert_eq!(results.len(), 1, "{label}");
            assert_eq!(results[0].outcome, VerificationOutcome::Unknown, "{label}");
            assert_eq!(boundary.withheld_relabelled, usize::from(favorable_at_boundary), "{label}");
            assert_eq!(boundary.withheld_relabelled_runtime_checked, 0, "{label}");
            assert_eq!(boundary.published_favorable, 0, "{label}");
            assert_eq!(boundary.unattributed_withheld(), 0, "{label}");
        }
        // Positive control on the identical path: the untouched row relabels.
        let mut results = vec![transport_to_verification_result(&function, &base, None, None)];
        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut results, None);
        assert_eq!(results[0].outcome, VerificationOutcome::RuntimeChecked);
        assert_eq!(boundary.withheld_relabelled_runtime_checked, 1);
    }

    /// The ticket itself: the human terminal used to say NOTHING about any of
    /// this. `terminal_result_line` renders label/kind/message/location/solver/
    /// time and never `reason`, and `Summary:` has no withheld bucket — so a
    /// demoted row read exactly like a solver `unknown`, and a deleted one like
    /// an obligation that never existed. Separate diagnostic identity retention
    /// now also makes the elided requests actionable.
    #[test]
    fn the_terminal_report_discloses_the_publication_boundary() {
        let mut results = vec![
            publishing_bounds_sibling(),
            evidence_free_bounds_twin(trust_types::Outcome::Proved),
        ];
        let boundary =
            crate::types::normalize_authenticated_results_for_publication(&mut results, None);
        let mut report = report_with_results_and_diagnostics(results, Vec::new());
        report.publication_boundary = Some(boundary);

        let rendered = report.terminal_lines().join("\n");
        assert!(
            rendered.contains("Publication boundary:"),
            "the terminal must name the boundary at all; got:\n{rendered}"
        );
        assert!(
            rendered.contains("2 obligation(s) passed the compiler")
                && rendered.contains("1 published")
                && rendered.contains("1 WITHHELD"),
            "the terminal must report compiler-passed vs published and the delta; got:\n{rendered}"
        );
        assert!(
            rendered.contains("1 deleted as a redundant alias"),
            "the DELETED fate is the one no other view can show, so it must be named \
             explicitly; got:\n{rendered}"
        );
        assert!(
            rendered.contains("0 relabelled unknown"),
            "and the split must be stated even when one side is zero; got:\n{rendered}"
        );
    }

    /// A report that never went through a publication pass says so rather than
    /// printing a zero: "0 withheld" and "not measured" are different claims.
    #[test]
    fn an_unmeasured_publication_boundary_is_disclosed_as_unmeasured() {
        let report =
            report_with_results_and_diagnostics(vec![publishing_bounds_sibling()], Vec::new());
        assert_eq!(report.publication_boundary, None);
        let rendered = report.terminal_lines().join("\n");
        assert!(rendered.contains("Publication boundary: not measured"), "got:\n{rendered}");
        assert!(
            !rendered.contains("0 withheld"),
            "an unmeasured boundary must never render as a clean zero; got:\n{rendered}"
        );
    }

    #[test]
    fn clean_cic_v2_rejects_missing_forged_and_mismatched_identities() {
        let assert_rejected = |transport: trust_types::TransportObligationResult, label: &str| {
            let result =
                transport_to_verification_result("crate::paths::render", &transport, None, None);
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

        // KR0 switch: the same row with its evidence unstamped (a row written
        // before the switch, or a mint that bypassed the reference entry) is
        // not Certified and is withheld; the stamped fixture is the control
        // the positive tests above publish.
        let mut unstamped = clean_cic_hardened_transport();
        let proof = unstamped.proof_evidence.as_mut().expect("proof");
        proof.evidence =
            proof.evidence.as_ref().map(trust_types::ProofEvidence::without_kernel_reference);
        assert_rejected(unstamped, "evidence naming no reference kernel theory");
    }

    #[test]
    fn actual_add1_replay_observation_preserves_clean_cic_publication() {
        let capture: serde_json::Value = serde_json::from_str(include_str!(
            "report/fixtures/native-add1-replay-publication.json"
        ))
        .unwrap();
        for row in capture["obligations"].as_array().unwrap() {
            // The public report's display kind is not the native wire tag.
            // Recover that exact existing mapping from the retained typed kind.
            let kind: trust_types::VcKind =
                serde_json::from_value(row["transport_evidence"]["typed_kind"].clone()).unwrap();
            let result = VerificationResult {
                function: capture["function"].as_str().unwrap().into(),
                kind: kind.transport_tag().into(),
                message: kind.description(),
                outcome: VerificationOutcome::Proved,
                backend: "clean-kernel".into(),
                time_ms: Some(0),
                location: Some(serde_json::from_value(row["location"].clone()).unwrap()),
                counterexample: None,
                reason: None,
                raw_line: format!(
                    "targo-trust-structured-transport-evidence:{}",
                    row["transport_evidence"]
                ),
            };
            let structured = structured_transport_evidence(&result).unwrap();
            let proof = structured.proof_evidence.as_ref().unwrap();
            assert_eq!(proof.diagnostics.len(), 1);
            assert!(
                clean_cic_transport_proof_is_publishable(&result, proof),
                "actual public replay proof must remain attachable: {}",
                result.kind
            );
            let mut legacy = proof.clone();
            legacy.diagnostics.clear();
            assert!(clean_cic_transport_proof_is_publishable(&result, &legacy));

            let reject = |label: &str, changed: &TransportProofEvidence| {
                assert!(
                    !clean_cic_transport_proof_is_publishable(&result, changed),
                    "{label} must not publish: {}",
                    result.kind
                );
            };
            for (label, key, value) in [
                ("outer version", "version", serde_json::json!(2)),
                ("foreign subject", "subject", serde_json::json!("other")),
                ("foreign row", "obligation_id", serde_json::json!("other")),
                ("foreign claim", "claim_digest_sha256", serde_json::json!("0".repeat(64))),
                ("outer extra field", "extra", serde_json::json!(true)),
            ] {
                let mut changed = proof.clone();
                let diagnostic = &mut changed.diagnostics[0];
                let mut detail: serde_json::Value =
                    serde_json::from_str(diagnostic.detail.as_deref().unwrap()).unwrap();
                detail[key] = value;
                diagnostic.detail = Some(detail.to_string());
                reject(label, &changed);
            }
            for (key, value) in [
                ("schema", serde_json::json!(2)),
                ("kind", serde_json::json!("saved_verdict")),
                ("function", serde_json::json!("other")),
                ("full_vc_sha256", serde_json::json!("0".repeat(64))),
                ("proof_evidence_sha256", serde_json::json!("0".repeat(64))),
                ("lineage_sha256", serde_json::json!("0".repeat(64))),
                ("extra", serde_json::json!(true)),
            ] {
                let mut changed = proof.clone();
                let diagnostic = &mut changed.diagnostics[0];
                let mut detail: serde_json::Value =
                    serde_json::from_str(diagnostic.detail.as_deref().unwrap()).unwrap();
                detail["replay"][key] = value;
                diagnostic.detail = Some(detail.to_string());
                reject(key, &changed);
            }
            let mut duplicate = proof.clone();
            duplicate.diagnostics.push(duplicate.diagnostics[0].clone());
            reject("duplicate audit", &duplicate);
            let mut unknown = proof.clone();
            unknown.diagnostics[0].code = "other".into();
            reject("unknown diagnostic", &unknown);
            for severity in [
                trust_types::TransportEvidenceDiagnosticSeverity::Warning,
                trust_types::TransportEvidenceDiagnosticSeverity::Error,
            ] {
                let mut changed = proof.clone();
                changed.diagnostics[0].severity = severity;
                reject("noninformational diagnostic", &changed);
            }
            for detail in [None, Some("{}".into()), Some("not-json".into())] {
                let mut changed = proof.clone();
                changed.diagnostics[0].detail = detail;
                reject("missing or malformed binding", &changed);
            }
            let mut changed = proof.clone();
            changed.artifacts[0].metadata.as_mut().unwrap()["CleanCic"]["term"][0] =
                serde_json::json!(255);
            reject("changed evidence", &changed);

            for mutation in ["absent", "changed", "foreign"] {
                let mut changed = result.clone();
                let mut payload = row["transport_evidence"].clone();
                match mutation {
                    "absent" => {
                        payload.as_object_mut().unwrap().remove("original_vc_snapshot");
                    }
                    "changed" => {
                        payload["original_vc_snapshot"]["original_vc_json"] =
                            serde_json::json!("{}");
                    }
                    "foreign" => {
                        payload["original_vc_snapshot"]["claim_digest_sha256"] =
                            serde_json::json!("0".repeat(64));
                    }
                    _ => unreachable!(),
                }
                changed.raw_line = format!("targo-trust-structured-transport-evidence:{payload}");
                assert!(!clean_cic_transport_proof_is_publishable(&changed, proof), "{mutation}");
            }

            // The diagnostic matcher compares the observation to the snapshot,
            // not to a lossy rendering of the full target-scoped function. The
            // original live row receipt binds that identity and the typed kind.
            // This fixture helper models receipt minting only inside tests;
            // actual source/session admission remains the production channel.
            let report = with_live_transport_authority(report_with_result(
                result.clone(),
                VerificationOutcome::Proved,
            ));
            assert_eq!(report.to_trust_report().summary.total_proved, 1);
            let mut changed = report.clone();
            changed.results[0].function.push_str("::foreign");
            let canonical = changed.to_trust_report();
            assert_eq!(canonical.summary.total_proved, 0);
            assert_eq!(canonical.summary.total_unknown, 1);
            assert!(canonical.functions[0].obligations[0].proof_evidence.is_none());

            let mut changed = report.clone();
            let mut payload = row["transport_evidence"].clone();
            let other = capture["obligations"]
                .as_array()
                .unwrap()
                .iter()
                .find(|other| other["kind"] != row["kind"])
                .unwrap();
            payload["typed_kind"] = other["transport_evidence"]["typed_kind"].clone();
            changed.results[0].raw_line =
                format!("targo-trust-structured-transport-evidence:{payload}");
            let canonical = changed.to_trust_report();
            assert_eq!(canonical.summary.total_proved, 0);
            assert_eq!(canonical.summary.total_unknown, 1);
            assert!(canonical.functions[0].obligations[0].proof_evidence.is_none());
        }
    }

    /// The wire row the compiler emits for an E9 kernel discharge of an
    /// `ensures` clause (`clean-kernel-citation` = cited theorem re-check,
    /// `clean-kernel-defeq` = uncited island definitional equality): a typed
    /// `postcondition`, and — when `with_evidence` — the content-addressed
    /// `clean_cic` artifact the compiler now attaches. The payload has the E9
    /// lane's shape (`trust_certify::clean_island::certify_ensures_discharge`):
    /// a serialized proof term, and a `context` that is that lane's binding
    /// record rather than a `ReducedContext`. This consumer is schema-agnostic
    /// about `context` on purpose — it checks the typed CleanCic carrier and its
    /// content address, never the kernel judgment, exactly as for every other
    /// `clean_cic` row.
    fn e9_ensures_discharge_transport(
        solver: &str,
        with_evidence: bool,
    ) -> trust_types::TransportObligationResult {
        let mut transport = clean_cic_hardened_transport();
        transport.obligation_id = Some("vc:crate::keep:postcondition:0".into());
        transport.kind = trust_types::VcKind::Postcondition.transport_tag();
        transport.typed_kind = Some(Box::new(trust_types::VcKind::Postcondition));
        transport.description = trust_types::VcKind::Postcondition.description();
        transport.solver = solver.into();
        transport.time_ms = 0;
        if !with_evidence {
            transport.proof_evidence = None;
            return transport;
        }
        let mut context = b"trust-certify.e9-ensures-discharge.context.v1\0".to_vec();
        context.extend_from_slice(&[7, 0, 0, 0, 0, 0, 0, 0]);
        context.extend_from_slice(b"keep_fn");
        let evidence = trust_ir::ProofEvidence::CleanCic {
            term: vec![3, 1, 4, 1, 5, 9, 2, 6],
            context,
            lineage: trust_ir::ProofDigest::sha256([0xe9; 32]),
            kernel_recheck: None,
        };
        let payload =
            serde_json::to_value(&evidence).expect("serialize typed CleanCic test payload");
        let bytes = compiler_clean_cic_payload_bytes(&evidence);
        let digest = trustc_domain_length_bound_sha256_hex("trustc.transport-clean-cic.v2", &bytes);
        let proof_id = format!("clean-cic:v2:{digest}");
        let proof = transport.proof_evidence.as_mut().expect("template proof");
        proof.proof_id = Some(proof_id.clone());
        let artifact = &mut proof.artifacts[0];
        artifact.artifact_id = Some(proof_id);
        artifact.digest.as_mut().expect("template digest").value = digest.clone();
        artifact.uri = Some(format!("trust-certify://clean-cic/{digest}"));
        artifact.metadata = Some(payload);
        transport
    }

    /// Trust (E9 evidence; `wf1-probe-package` finding a2): the authenticated
    /// lane graded EVERY contract discharged by a Lean definition or theorem
    /// `unknown` — raw `trustc` said "2 kernel-certified", the wire rows were
    /// `proved` by `clean-kernel-defeq` / `clean-kernel-citation`, and they
    /// carried no `proof_evidence`, so publication withheld all of them. The
    /// consumer was right and is UNCHANGED; the compiler now attaches the
    /// kernel-audited `clean_cic` artifact. Through the full production path:
    ///
    /// * positive: both E9 solver spellings publish as `proved` with their
    ///   content-addressed proof identity;
    /// * close negative twin: the identical row WITHOUT the artifact is still
    ///   withheld (`unknown`, not policy-B runtime-checked — a postcondition
    ///   keeps no rustc runtime check);
    /// * tamper controls: a payload edited after addressing, a payload swapped
    ///   under another payload's identity, and an emptied proof term are all
    ///   withheld.
    ///
    /// What this consumer does NOT detect, by design and for every `clean_cic`
    /// row alike: a wholly self-consistent envelope lifted from another row. It
    /// never re-runs the kernel and does not hold the obligation; that binding
    /// is the compiler's (`kernel_evidence_for` hands out a payload only through
    /// the exact sealed row) and `trust_certify`'s `recheck_ensures_discharge`.
    #[test]
    fn e9_ensures_discharge_rows_publish_only_with_their_clean_cic_artifact() {
        for solver in ["clean-kernel-citation", "clean-kernel-defeq"] {
            let transport = e9_ensures_discharge_transport(solver, true);
            let proof_id = transport
                .proof_evidence
                .as_ref()
                .and_then(|proof| proof.proof_id.clone())
                .expect("content-addressed proof ID");
            let result = transport_to_verification_result("crate::keep", &transport, None, None);
            let report = with_live_transport_authority(report_with_result(
                result,
                VerificationOutcome::Proved,
            ));
            assert_eq!(report.results.len(), 1);
            assert_eq!(report.results[0].outcome, VerificationOutcome::Proved, "{solver}");
            let boundary = report.publication_boundary.clone().expect("publication boundary");
            assert_eq!(boundary.compiler_favorable, 1);
            assert_eq!(boundary.published_favorable, 1, "{solver} must publish");
            assert_eq!(boundary.withheld_relabelled, 0);
            let obligation = report.to_trust_report().functions.remove(0).obligations.remove(0);
            let published = obligation.proof_evidence.expect("published proof evidence");
            assert_eq!(published.proof_id.as_deref(), Some(proof_id.as_str()));
            assert_eq!(published.backend, "clean-kernel");
            assert_eq!(published.artifacts.len(), 1);

            // Close negative twin: the measured pre-fix wire row.
            let bare = e9_ensures_discharge_transport(solver, false);
            let result = transport_to_verification_result("crate::keep", &bare, None, None);
            let report = with_live_transport_authority(report_with_result(
                result,
                VerificationOutcome::Proved,
            ));
            assert_eq!(report.results[0].outcome, VerificationOutcome::Unknown, "{solver}");
            let reason = report.results[0].reason.clone().unwrap_or_default();
            assert!(
                reason.contains("without attachable native or clean-kernel proof evidence"),
                "{reason}"
            );
            let boundary = report.publication_boundary.clone().expect("publication boundary");
            assert_eq!(boundary.published_favorable, 0);
            assert_eq!(boundary.withheld_relabelled, 1);
            assert_eq!(boundary.withheld_relabelled_runtime_checked, 0);
        }

        let assert_withheld = |transport: trust_types::TransportObligationResult, label: &str| {
            let result = transport_to_verification_result("crate::keep", &transport, None, None);
            let report = with_live_transport_authority(report_with_result(
                result,
                VerificationOutcome::Proved,
            ));
            assert_eq!(
                report.results[0].outcome,
                VerificationOutcome::Unknown,
                "{label} must be WITHHELD"
            );
            let boundary = report.publication_boundary.clone().expect("publication boundary");
            assert_eq!(boundary.published_favorable, 0, "{label}");
            assert!(
                promoted_proof_evidence_for_transport(transport).is_none(),
                "{label} must not reach obligation publication"
            );
        };

        // The proof term edited AFTER the payload was content-addressed.
        let mut edited = e9_ensures_discharge_transport("clean-kernel-citation", true);
        let artifact = &mut edited.proof_evidence.as_mut().expect("proof").artifacts[0];
        artifact.metadata.as_mut().expect("payload")["CleanCic"]["term"][0] = serde_json::json!(4);
        assert_withheld(edited, "a payload edited after addressing");

        // Another row's (self-consistent) payload under THIS row's identity.
        let mut swapped = e9_ensures_discharge_transport("clean-kernel-citation", true);
        let foreign = clean_cic_hardened_transport();
        swapped.proof_evidence.as_mut().expect("proof").artifacts[0].metadata =
            foreign.proof_evidence.expect("foreign proof").artifacts[0].metadata.clone();
        assert_withheld(swapped, "a payload swapped under another identity");

        // A coherently re-addressed payload whose proof term is EMPTY.
        let mut emptied = e9_ensures_discharge_transport("clean-kernel-defeq", true);
        let proof = emptied.proof_evidence.as_mut().expect("proof");
        let mut payload = proof.artifacts[0].metadata.clone().expect("payload");
        payload["CleanCic"]["term"] = serde_json::json!([]);
        let emptied_evidence: trust_ir::ProofEvidence =
            serde_json::from_value(payload.clone()).expect("the emptied payload still decodes");
        let bytes = compiler_clean_cic_payload_bytes(&emptied_evidence);
        let digest = trustc_domain_length_bound_sha256_hex("trustc.transport-clean-cic.v2", &bytes);
        let forged_id = format!("clean-cic:v2:{digest}");
        proof.proof_id = Some(forged_id.clone());
        proof.artifacts[0].artifact_id = Some(forged_id);
        proof.artifacts[0].digest.as_mut().expect("digest").value = digest.clone();
        proof.artifacts[0].uri = Some(format!("trust-certify://clean-cic/{digest}"));
        proof.artifacts[0].metadata = Some(payload);
        assert_withheld(emptied, "a coherently addressed EMPTY proof term");
    }

    #[test]
    fn hardened_duplicate_representative_prefers_publishable_clean_cic() {
        for publishable_first in [false, true] {
            let mut evidence_less = clean_cic_hardened_transport();
            evidence_less.proof_evidence.as_mut().expect("proof").proof_id = None;
            let evidence_less = transport_to_verification_result(
                "crate::paths::render",
                &evidence_less,
                None,
                None,
            );
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
    /// A compiler-declared design mandate: an L1 profile rule (`Result::ok`
    /// discarding an error under `unix_hardened`). Before G3-MANDATE-L1-ONLY-1
    /// this fixture was the `[unsafe] missing SAFETY comment` stand-in, an L0
    /// modelling gap that is no longer a mandate
    /// (`l0_unsafe_or_ffi_row_with_the_mandate_bit_is_not_a_mandate`).
    fn design_mandate_result() -> VerificationResult {
        design_mandate_result_of(
            "hardened_error_discard",
            "hardened boundary (error_discard): core::result::Result::<T, E>::ok: error discarded",
        )
    }

    fn design_mandate_result_of(kind: &str, description: &str) -> VerificationResult {
        let transport = trust_types::TransportObligationResult {
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: None,
            claim_digest_sha256: None,
            kind: kind.into(),
            original_vc_snapshot: None,
            typed_kind: None,
            description: description.into(),
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
            grade: None,
        };
        transport_to_verification_result("crate::uses_unsafe", &transport, None, None)
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
        assert_eq!(
            report.canonical_report_state_divergence(&canonical),
            None,
            "canonical mandate counts must remain aligned with the sealed internal partition"
        );
    }

    /// G3-MANDATE-L1-ONLY-1: an L0 `UnsafeOperation`/`FfiBoundary` row that
    /// carries the compiler's `design_mandate` bit (the shape an older compiler
    /// published for an FFI call with no summary or the `[unsafe] missing SAFETY
    /// comment` stand-in) is NOT a design mandate: the gate keeps it `unknown`,
    /// the canonical report keeps it `unknown`, and the seal still succeeds
    /// because the two agree. An L1 rule with the same bit beside it stays a
    /// mandate (the positive control in the same report).
    #[test]
    fn l0_unsafe_or_ffi_row_with_the_mandate_bit_is_not_a_mandate() {
        let safety_stand_in = design_mandate_result_of(
            "hardened_unsafe_operation",
            "assertion: [unsafe] missing SAFETY comment on unsafe block",
        );
        let mut ffi_gap = design_mandate_result_of(
            "hardened_ffi_boundary",
            "FFI boundary violation: getpgrp: no summary: behavior unmodeled, cannot prove safe",
        );
        let ffi_kind = VcKind::FfiBoundaryViolation {
            callee: "getpgrp".into(),
            desc: "no summary: behavior unmodeled, cannot prove safe".into(),
        };
        let mut evidence = structured_transport_evidence(&ffi_gap).expect("structured row");
        evidence.typed_kind = Some(Box::new(ffi_kind.clone()));
        crate::types::replace_structured_transport_evidence(&mut ffi_gap, &evidence)
            .expect("replace structured evidence");
        ffi_gap.kind = ffi_kind.transport_tag();
        ffi_gap.message = ffi_kind.description();
        // Each row is authority-safe and resolves to its L0 category, so the
        // only thing refusing the mandate below is the L1-only filter.
        assert_eq!(exact_transport_vc_kind(&ffi_gap), Ok(Some(ffi_kind)));
        assert_eq!(
            parse_hardened_category(&safety_stand_in.kind),
            Some(HardenedVcCategory::UnsafeOperation)
        );
        for gap in [&safety_stand_in, &ffi_gap] {
            assert!(crate::types::structured_transport_vc_kind_is_authority_safe(gap), "{gap:?}");
            assert!(
                structured_transport_evidence(gap).is_some_and(|evidence| evidence.design_mandate),
                "the fixture carries the raw bit: {gap:?}",
            );
            assert!(hardened_mandate_category(gap).is_none(), "{gap:?}");
            assert!(!transport_design_mandate(gap), "{gap:?}");
            assert!(!crate::pipeline::hardened::counts_as_design_mandate(gap), "{gap:?}");
        }
        assert!(transport_design_mandate(&design_mandate_result()), "positive control");

        let report = with_live_transport_authority(report_with_results_and_diagnostics(
            vec![safety_stand_in, ffi_gap, design_mandate_result()],
            vec![],
        ));
        assert_eq!(report.mandated, 1, "only the L1 rule is a mandate");
        assert_eq!(report.unknown, 2, "the two L0 gaps stay unknown");
        assert!(!report.success);

        let canonical = report.to_trust_report();
        assert_eq!(canonical.summary.total_design_requirements, 1);
        assert_eq!(canonical.summary.total_unknown, 2);
        assert_eq!(canonical.summary.verdict, trust_types::CrateVerdict::Inconclusive);
        assert_eq!(report.canonical_report_state_divergence(&canonical), None);
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
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: None,
            claim_digest_sha256: None,
            kind: kind.transport_tag(),
            original_vc_snapshot: None,
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
            grade: None,
        };
        transport_to_verification_result(function, &transport, None, None)
    }

    fn failed_gate(failed: usize, total: usize) -> trust_types::VerificationGateReport {
        trust_types::VerificationGateReport {
            lane: "advisory".into(),
            verification_level: Some("L2".into()),
            decision: "fail".into(),
            exit_code: 1,
            counts: trust_types::VerificationGateCounts {
                total,
                proved: 0,
                failed,
                unknown: total - failed,
                runtime_checked: 0,
                assumed: 0,
                mandated: 0,
                contract_panics: 0,
                excluded: 0,
            },
            conditional_on_assumption_rows: false,
            conditional_on_dependency_entries: false,
            conditional_on_runtime_checks: false,
            conditional_on_unknown_rows: false,
            conditional_on_visitation_entries: false,
            coverage: None,
            test_execution: None,
            exclusions: Vec::new(),
            determinism: None,
            failure_sites: None,
            project_requirements: None,
        }
    }

    /// A refuted MIR assert under the hardened profile: the L0 overflow row and
    /// its `hardened_panic_boundary` twin, at one span.
    fn assert_twin_rows(
        primary_outcome: trust_types::Outcome,
        twin_outcome: trust_types::Outcome,
    ) -> Vec<VerificationResult> {
        let span = SourceSpan {
            file: "src/subject.rs".into(),
            line_start: 21,
            col_start: 43,
            line_end: 21,
            col_end: 50,
        };
        let mut primary = typed_transport_result(
            "m::split",
            VcKind::ArithmeticOverflow {
                op: trust_types::BinOp::Add,
                operand_tys: (trust_types::Ty::usize(), trust_types::Ty::usize()),
            },
            "ay-in-process",
            primary_outcome,
        );
        primary.location = Some(span.clone());
        let mut twin = typed_transport_result(
            "m::split",
            VcKind::HardenedBoundary {
                category: trust_types::HardenedVcCategory::PanicBoundary,
                callee: "mir_assert::Overflow(Add)".into(),
                detail: "MIR arithmetic assert can panic; hardened code needs proven arithmetic \
                         preconditions"
                    .into(),
            },
            "ay-in-process",
            twin_outcome,
        );
        twin.location = Some(span);
        vec![with_stable_key(primary, 0), with_stable_key(twin, 0)]
    }

    /// Reporting hazard "each defect is counted twice" (survey RANKED.md §5):
    /// the two rows are DISTINCT obligations (L0 safety may be runtime-checked;
    /// panic-freedom never is), so both stay and both stay failed. The gate now
    /// also records that they are one site, and links them.
    ///
    /// CONTROL: the gate's counts, decision and exit code are byte-identical
    /// before and after the accounting is recorded, and every lane still FAILS
    /// on the partition of these rows.
    #[test]
    fn failure_sites_link_a_failed_assert_twin_and_leave_the_gate_unchanged() {
        use crate::pipeline::hardened::{
            GateDecision, GateLane, evaluate_verification_gate, partition_outcome_counts,
        };
        let rows = assert_twin_rows(trust_types::Outcome::Failed, trust_types::Outcome::Failed);
        let (counts, defects) = partition_outcome_counts(&rows);
        assert!(defects.is_empty(), "{defects:?}");
        assert_eq!((counts.total, counts.failed), (2, 2), "both rows stay failed");
        for lane in [GateLane::Advisory, GateLane::MemorySafe, GateLane::Strict, GateLane::Certify]
        {
            assert_eq!(evaluate_verification_gate(lane, 0, counts), GateDecision::Fail, "{lane:?}");
        }

        let mut report = report_with_results_and_diagnostics(rows, vec![]);
        report.gate = Some(failed_gate(2, 2));
        let before = report.gate.clone().unwrap();
        report.record_determinism();
        let gate = report.gate.as_ref().unwrap();
        assert_eq!(gate.counts, before.counts);
        assert_eq!(gate.decision, before.decision);
        assert_eq!(gate.exit_code, before.exit_code);

        let sites = gate.failure_sites.as_ref().expect("failure sites recorded");
        assert_eq!(sites.failed_rows, gate.counts.failed);
        assert_eq!((sites.distinct_sites, sites.hardened_twin_rows), (1, 1));
        let link = &sites.twin_links[0];
        assert_eq!(link.function, "m::split");
        assert_eq!(link.primary_kind, "arithmetic_overflow_add");
        assert_eq!(link.hardened_callee, "mir_assert::Overflow(Add)");

        let rendered = report.terminal_lines().join("\n");
        assert!(rendered.contains("Summary: 0 proved, 2 failed"), "{rendered}");
        assert!(
            rendered
                .contains("Failed sites: 2 failed row(s) at 1 distinct source site(s); 1 row(s)"),
            "{rendered}"
        );
        let json = serde_json::to_string(gate).unwrap();
        assert!(
            json.contains("\"failure_sites\":{\"failed_rows\":2,\"distinct_sites\":1"),
            "{json}"
        );
    }

    /// CONTROL: a twin whose L0 row did NOT fail is a failure in its own right
    /// (the panic is reachable). It is never linked away, the site view adds no
    /// line, and the gate still fails.
    #[test]
    fn a_failed_twin_without_a_failed_primary_is_not_linked() {
        use crate::pipeline::hardened::{
            GateDecision, GateLane, evaluate_verification_gate, partition_outcome_counts,
        };
        let rows = assert_twin_rows(trust_types::Outcome::Unknown, trust_types::Outcome::Failed);
        let (counts, _) = partition_outcome_counts(&rows);
        assert_eq!(counts.failed, 1);
        assert_eq!(evaluate_verification_gate(GateLane::Advisory, 0, counts), GateDecision::Fail);
        let mut report = report_with_results_and_diagnostics(rows, vec![]);
        report.gate = Some(failed_gate(1, 2));
        report.record_determinism();
        let sites = report.gate.as_ref().unwrap().failure_sites.clone().unwrap();
        assert_eq!((sites.failed_rows, sites.distinct_sites, sites.hardened_twin_rows), (1, 1, 0));
        assert!(!report.terminal_lines().iter().any(|line| line.starts_with("Failed sites:")));
    }

    /// Review defect (2026-10-02): two `+` asserts expanded from one macro call
    /// site share a byte-identical span. Assert A's L0 row proved and its twin
    /// failed; assert B's L0 row failed and its twin proved. That is TWO refuted
    /// asserts. Pairing only the FAILED rows in row order linked A's twin to B's
    /// L0 row and read them as one. The pairing now sees every row at the key, like
    /// `subsume_hardened_panic_twins`: more than one candidate on either side is
    /// ambiguous and links nothing. Counts and the gate are unchanged.
    #[test]
    fn twins_of_different_asserts_at_one_span_are_never_linked() {
        let mut rows = assert_twin_rows(trust_types::Outcome::Proved, trust_types::Outcome::Failed);
        rows.extend(assert_twin_rows(trust_types::Outcome::Failed, trust_types::Outcome::Proved));
        let (counts, _) = crate::pipeline::hardened::partition_outcome_counts(&rows);
        assert_eq!(counts.failed, 2);
        let mut report = report_with_results_and_diagnostics(rows, vec![]);
        report.gate = Some(failed_gate(2, 4));
        let before = report.gate.clone().unwrap();
        report.record_determinism();
        let gate = report.gate.as_ref().unwrap();
        assert_eq!(
            (gate.counts, &gate.decision, gate.exit_code),
            (before.counts, &before.decision, before.exit_code)
        );
        let sites = gate.failure_sites.clone().unwrap();
        assert_eq!((sites.failed_rows, sites.distinct_sites, sites.hardened_twin_rows), (2, 1, 0));
        assert!(sites.twin_links.is_empty(), "{:?}", sites.twin_links);
    }

    /// The pairing reads `PanicTwinFamily`, the subsumption pass's classifier,
    /// over the twin callee vcgen really mints (`hardened_mir_assert_callee`):
    /// every family links with its own L0 kind and with no other operation.
    /// `OverflowNeg` does not link: the subsumption classifier has no
    /// `negation_overflow` sibling either, so the accounting under-links there
    /// (both rows stay counted) rather than holding a second family table.
    #[test]
    fn failure_sites_pair_each_assert_family_through_the_subsumption_classifier() {
        use trust_types::{AssertMessage, BinOp, Ty};
        let u32s = || (Ty::u32(), Ty::u32());
        let shift = |op| VcKind::ShiftOverflow { op, operand_ty: Ty::u32(), shift_ty: Ty::u32() };
        let cases: Vec<(AssertMessage, VcKind, bool)> = vec![
            (AssertMessage::BoundsCheck, VcKind::IndexOutOfBounds, true),
            (AssertMessage::BoundsCheck, VcKind::SliceBoundsCheck, true),
            (AssertMessage::DivisionByZero, VcKind::DivisionByZero, true),
            (AssertMessage::RemainderByZero, VcKind::RemainderByZero, true),
            (
                AssertMessage::Overflow(BinOp::Add),
                VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: u32s() },
                true,
            ),
            (
                AssertMessage::Overflow(BinOp::Mul),
                VcKind::ArithmeticOverflow { op: BinOp::Mul, operand_tys: u32s() },
                true,
            ),
            (AssertMessage::Overflow(BinOp::Shl), shift(BinOp::Shl), true),
            (AssertMessage::Overflow(BinOp::Shr), shift(BinOp::Shr), true),
            // Cross-operation and cross-family: never.
            (
                AssertMessage::Overflow(BinOp::Add),
                VcKind::ArithmeticOverflow { op: BinOp::Sub, operand_tys: u32s() },
                false,
            ),
            (AssertMessage::Overflow(BinOp::Shl), shift(BinOp::Shr), false),
            (
                AssertMessage::Overflow(BinOp::Shl),
                VcKind::ArithmeticOverflow { op: BinOp::Shl, operand_tys: u32s() },
                false,
            ),
            (AssertMessage::BoundsCheck, VcKind::DivisionByZero, false),
            (AssertMessage::OverflowNeg, VcKind::NegationOverflow { ty: Ty::i32() }, false),
        ];
        let span = SourceSpan {
            file: "src/lib.rs".into(),
            line_start: 3,
            col_start: 9,
            line_end: 3,
            col_end: 14,
        };
        for (msg, primary_kind, links) in cases {
            let mut primary = typed_transport_result(
                "m::f",
                primary_kind.clone(),
                "ay-in-process",
                trust_types::Outcome::Failed,
            );
            primary.location = Some(span.clone());
            let mut twin = typed_transport_result(
                "m::f",
                VcKind::HardenedBoundary {
                    category: trust_types::HardenedVcCategory::PanicBoundary,
                    callee: trust_types::hardened_mir_assert_callee(&msg),
                    detail: "MIR assert can panic".into(),
                },
                "ay-in-process",
                trust_types::Outcome::Failed,
            );
            twin.location = Some(span.clone());
            let report = report_with_results_and_diagnostics(vec![primary, twin], vec![]);
            let sites = report.failure_sites();
            assert_eq!((sites.failed_rows, sites.distinct_sites), (2, 1), "{msg:?}");
            assert_eq!(
                sites.hardened_twin_rows,
                usize::from(links),
                "{msg:?} twin vs {primary_kind:?}: links={links}"
            );
        }
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
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: Some("vc:crate::contract:postcondition:0".into()),
            claim_digest_sha256: Some("a".repeat(64)),
            kind: "postcond".into(),
            original_vc_snapshot: None,
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
            grade: None,
        };
        let result = transport_to_verification_result("crate::contract", &transport, None, None);
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
        let mismatched =
            transport_to_verification_result("crate::contract", &transport, None, None);
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
            assumes: Vec::new(),
            gap_class: None,
            obligation_id: Some("vc:crate::contract:postcondition:0".into()),
            claim_digest_sha256: Some("a".repeat(64)),
            kind: kind.transport_tag(),
            original_vc_snapshot: None,
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
            grade: None,
        };
        let result = transport_to_verification_result("crate::contract", &transport, None, None);
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
        let result = transport_to_verification_result("crate::contract", &transport, None, None);

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
    // Trust (coroutine resume-state contract): same laundering guard as the
    // assumption rows below — the published contract row has nothing enforced
    // at runtime and carries no proof, so it must never be relabeled
    // RuntimeChecked (or, defectively, Proved) in report.json.
    #[test]
    fn coroutine_resume_contract_row_never_renders_as_runtime_checked() {
        let contract = VerificationResult {
            function: "crate::tick::{closure#0}".into(),
            kind: trust_types::assumption::COROUTINE_RESUME_CONTRACT_ROW_KIND.into(),
            message: trust_types::assumption::coroutine_resume_contract_row_description(&[0]),
            outcome: VerificationOutcome::Unknown,
            backend: trust_types::assumption::COROUTINE_RESUME_CONTRACT_ROW_SOLVER.into(),
            time_ms: Some(0),
            location: None,
            counterexample: None,
            reason: Some(trust_types::assumption::COROUTINE_RESUME_CONTRACT_ROW_REASON.into()),
            raw_line: String::new(),
        };
        let report = report_with_results_and_diagnostics(vec![contract], Vec::new());
        let trust_report = report.to_trust_report();

        assert_eq!(
            trust_report.summary.total_runtime_checked, 0,
            "a published contract row must not be counted as runtime-checked"
        );
        assert_ne!(trust_report.summary.verdict, trust_types::CrateVerdict::RuntimeChecked);
        assert!(
            !matches!(
                trust_report.functions[0].obligations[0].outcome,
                ObligationOutcome::Proved { .. }
            ),
            "a published contract row must never surface as a proved obligation"
        );
    }

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

    /// S9: a `-Ztrust-verify=off` unit whose codegen ran in an external backend
    /// (the trust-mc dylib) is not proof evidence. Its stderr carries trustc's
    /// zero-obligation note and Kani text, and at most a zero crate summary:
    /// no function_result row, and functions_verified = 0 in the proof report.
    #[test]
    fn external_backend_verify_off_unit_yields_no_function_rows_or_verified_functions() {
        for stderr in [
            crate::pipeline::kani_gate::EXTERNAL_BACKEND_VERIFY_OFF_STDERR,
            crate::pipeline::kani_gate::EXTERNAL_BACKEND_VERIFY_OFF_STDERR_WITH_ZERO_SUMMARY,
        ] {
            let parsed =
                crate::pipeline::parse_compiler_stderr(std::io::Cursor::new(stderr), false);
            assert!(
                parsed.verification_results.is_empty(),
                "Kani text became verification rows: {:?}",
                parsed.verification_results
            );
            let report = report_with_results_and_diagnostics(
                parsed.verification_results,
                parsed.compiler_diagnostics,
            );
            let canonical = report.to_trust_report();
            assert!(canonical.functions.is_empty(), "{:?}", canonical.functions);
            assert_eq!(canonical.summary.functions_verified, 0);
            assert_eq!(canonical.summary.total_proved, 0);
            assert_ne!(canonical.summary.verdict, trust_types::CrateVerdict::Verified);
        }
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

    // ---- Blocker 4 (2026-10-01): the store cap omits, it never discards ----

    /// Clears the cfg(test)-only policy hooks when a test ends, pass or panic.
    struct ArtifactHookGuard;

    impl Drop for ArtifactHookGuard {
        fn drop(&mut self) {
            test_hooks::ARTIFACT_STORE_POLICY.with(|cell| cell.set(None));
            test_hooks::INLINE_BUDGET_BYTES.with(|cell| cell.set(None));
            test_hooks::SAVED_NDJSON_BOUND_BYTES.with(|cell| cell.set(None));
            test_hooks::SAVED_HTML_BOUND_BYTES.with(|cell| cell.set(None));
        }
    }

    fn rendering_bounds(ndjson: Option<u64>, html: Option<u64>) -> ArtifactHookGuard {
        test_hooks::SAVED_NDJSON_BOUND_BYTES.with(|cell| cell.set(ndjson));
        test_hooks::SAVED_HTML_BOUND_BYTES.with(|cell| cell.set(html));
        ArtifactHookGuard
    }

    // ---- 2026-10-17: a derived rendering's size never discards report.json ----

    /// The NDJSON bound is derived from the canonical report it renders, never
    /// tighter than it. MEASURED on the 2026-10-16 candidate gate: aterm-gui's
    /// complete run (253,066 obligations) sealed its canonical report under
    /// `max_emitted_proof_report_bytes` and then lost everything to the flat
    /// 2 GiB NDJSON bound; aterm-serde's NDJSON/canonical ratio is 1.003.
    #[test]
    fn the_ndjson_bound_is_never_tighter_than_the_canonical_report() {
        use crate::input_limits::{
            MAX_SAVED_NDJSON_REPORT_BYTES, max_emitted_proof_report_bytes,
            max_saved_ndjson_report_bytes,
        };
        const GIB: usize = 1024 * 1024 * 1024;
        // The floor still holds for a small report.
        assert!(max_saved_ndjson_report_bytes(0) >= MAX_SAVED_NDJSON_REPORT_BYTES);
        // Never tighter than what the run may emit as its canonical report.
        assert!(max_saved_ndjson_report_bytes(0) >= max_emitted_proof_report_bytes());
        // Twice what this run actually emitted, whatever the machine.
        for canonical in [GIB, 3 * GIB, 7 * GIB, 40 * GIB] {
            let bound = max_saved_ndjson_report_bytes(canonical);
            assert!(bound >= 2 * canonical, "{canonical}: {bound}");
            // An honest rendering (the measured 1.003 ratio, with margin) fits.
            assert!(canonical + canonical / 100 <= bound, "{canonical}: {bound}");
        }
        // NEGATIVE CONTROL: the flat bound this replaced refuses a rendering of
        // a 3 GiB canonical report, which the derived bound admits.
        let rendering = 3 * GIB + 3 * GIB / 1000;
        assert!(rendering > MAX_SAVED_NDJSON_REPORT_BYTES);
        assert!(rendering <= max_saved_ndjson_report_bytes(3 * GIB));
    }

    /// Over its bound a rendering is SKIPPED: report.json is still written (and
    /// the other rendering with it), the skip is recorded in the sidecar, and the
    /// writer does not fail. Before 2026-10-17 either bound returned an error that
    /// discarded the whole bundle.
    #[test]
    fn an_oversized_rendering_is_skipped_and_never_discards_report_json() {
        let report = report_with_result(result_with_location(None), VerificationOutcome::Proved)
            .to_trust_report();
        let html = "<html>trust</html>";

        // Control: no hook, every artifact is written and nothing is skipped.
        let control = tempfile::tempdir().expect("control output");
        let status =
            write_report_artifacts_from_root(&report, control.path(), html, None, None, None)
                .expect("control bundle");
        assert!(status.skipped_renderings.is_empty());
        for name in ["report.json", "report.ndjson", "report.html"] {
            assert!(control.path().join(name).is_file(), "control: {name}");
        }
        assert!(read_sidecar(control.path()).get("skipped_renderings").is_none());

        // NDJSON over its bound: dropped, everything else written.
        let ndjson_capped = tempfile::tempdir().expect("ndjson-capped output");
        let status = {
            let _bounds = rendering_bounds(Some(1), None);
            write_report_artifacts_from_root(&report, ndjson_capped.path(), html, None, None, None)
                .expect("an oversized NDJSON must not fail the report transaction")
        };
        assert!(ndjson_capped.path().join("report.json").is_file());
        assert!(ndjson_capped.path().join("report.html").is_file());
        assert!(!ndjson_capped.path().join("report.ndjson").exists());
        assert_eq!(status.skipped_renderings.len(), 1);
        assert_eq!(status.skipped_renderings[0].artifact, "report.ndjson");
        assert_eq!(status.skipped_renderings[0].bound_bytes, 1);
        assert!(status.skipped_renderings[0].bytes > 1);
        assert!(status.complete, "a skipped rendering is not missing evidence");
        let sidecar = read_sidecar(ndjson_capped.path());
        assert_eq!(sidecar["skipped_renderings"][0]["artifact"], "report.ndjson");
        let _: trust_types::JsonProofReport = serde_json::from_slice(
            &fs::read(ndjson_capped.path().join("report.json")).expect("read report.json"),
        )
        .expect("report.json is the canonical report");
        let lines = skipped_rendering_lines(&status, ndjson_capped.path());
        assert_eq!(lines.len(), 1);
        assert!(lines[0].contains("SKIPPED") && lines[0].contains("report.ndjson"), "{lines:?}");

        // HTML over its bound: skipped, report.json and report.ndjson written.
        let html_capped = tempfile::tempdir().expect("html-capped output");
        let status = {
            let _bounds = rendering_bounds(None, Some(1));
            write_report_artifacts_from_root(&report, html_capped.path(), html, None, None, None)
                .expect("an oversized HTML must not fail the report transaction")
        };
        assert!(html_capped.path().join("report.json").is_file());
        assert!(html_capped.path().join("report.ndjson").is_file());
        assert!(!html_capped.path().join("report.html").exists());
        assert_eq!(status.skipped_renderings.len(), 1);
        assert_eq!(status.skipped_renderings[0].artifact, "report.html");
        assert_eq!(status.skipped_renderings[0].bytes, html.len() as u64);

        // A previous bundle's rendering does not survive beside a new report that
        // skipped it: the commit backs the old one up and installs only what was
        // staged.
        let stale = tempfile::tempdir().expect("stale output");
        write_report_artifacts_from_root(
            &report,
            stale.path(),
            "<html>old</html>",
            None,
            None,
            None,
        )
        .expect("first bundle");
        {
            let _bounds = rendering_bounds(None, Some(1));
            write_report_artifacts_from_root(&report, stale.path(), html, None, None, None)
                .expect("second bundle");
        }
        assert!(!stale.path().join("report.html").exists(), "the old HTML must not linger");
        assert!(stale.path().join("report.json").is_file());
    }

    fn artifact_store_policy(copy_cap_bytes: u64, link: bool) -> ArtifactHookGuard {
        test_hooks::ARTIFACT_STORE_POLICY.with(|cell| {
            cell.set(Some(ArtifactStorePolicy { copy_cap_bytes, link_from_private_store: link }));
        });
        ArtifactHookGuard
    }

    fn path_backed_artifacts_mut(
        obligation: &mut trust_types::ObligationReport,
    ) -> Vec<&mut trust_types::TransportEvidenceArtifact> {
        let mut out = Vec::new();
        if let Some(proof) = obligation.proof_evidence.as_mut() {
            out.extend(proof.artifacts.iter_mut());
            if let Some(native) = proof.native_trust_ir.as_mut() {
                out.extend(native.artifacts.iter_mut());
            }
        }
        if let Some(transport) = obligation.transport_evidence.as_mut() {
            if let Some(native) = transport.native_trust_ir.as_mut() {
                out.extend(native.artifacts.iter_mut());
            }
            if let Some(proof) = transport.proof_evidence.as_mut() {
                out.extend(proof.artifacts.iter_mut());
            }
        }
        out.retain(|artifact| {
            artifact
                .materialization
                .as_ref()
                .is_some_and(|materialization| materialization.materialized_path.is_some())
        });
        out
    }

    /// Insert, BEFORE the proved row, an UNKNOWN row whose path-backed
    /// artifact is `bytes` (written into `source_root`'s store). Returns its
    /// digest.
    fn insert_unknown_row_with_own_artifact(
        canonical: &mut trust_types::JsonProofReport,
        source_root: &Path,
        bytes: &[u8],
    ) -> String {
        let digest = trust_types::digest::lowercase_hex(&Sha256::digest(bytes));
        let store =
            source_root.join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256");
        fs::create_dir_all(&store).expect("create test store");
        fs::write(store.join(&digest), bytes).expect("write unknown-row artifact");
        let mut function = canonical.functions[0].clone();
        function.function = "crate::unknown_row".to_string();
        let obligation = &mut function.obligations[0];
        obligation.outcome = ObligationOutcome::Unknown { reason: "test unknown".to_string() };
        obligation.evidence = None;
        let artifacts = path_backed_artifacts_mut(obligation);
        assert!(!artifacts.is_empty(), "fixture should have a path-backed artifact");
        let original = artifacts[0].digest.clone().expect("digest").value;
        // Every occurrence (proof and transport evidence) names one artifact.
        for artifact in artifacts {
            assert_eq!(artifact.digest.as_ref().expect("digest").value, original);
            artifact.digest.as_mut().expect("digest").value = digest.clone();
            let materialization = artifact.materialization.as_mut().expect("materialization");
            materialization.byte_len = bytes.len() as u64;
            materialization.materialized_path = Some(format!(
                "{}/sha256/{digest}",
                trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY
            ));
        }
        canonical.functions.insert(0, function);
        canonical.recompute_summaries_from_obligation_outcomes();
        digest
    }

    fn proved_artifact_len(canonical: &trust_types::JsonProofReport) -> u64 {
        let function = canonical
            .functions
            .iter()
            .find(|function| {
                matches!(function.obligations[0].outcome, ObligationOutcome::Proved { .. })
            })
            .expect("proved row");
        let mut obligation = function.obligations[0].clone();
        let artifacts = path_backed_artifacts_mut(&mut obligation);
        artifacts[0].materialization.as_ref().expect("materialization").byte_len
    }

    /// The PRODUCTION shape of an over-budget report: the seal kept the
    /// artifact path-backed in the private store (inline budget 0), and this
    /// is the exact sealed canonical DTO `render` would write.
    fn sealed_store_backed_canonical_report(
        source_root: &Path,
    ) -> (trust_types::JsonProofReport, trust_types::TransportArtifactDigest) {
        test_hooks::INLINE_BUDGET_BYTES.with(|cell| cell.set(Some(0)));
        let (report, digest) = sealed_path_backed_native_report(source_root);
        test_hooks::INLINE_BUDGET_BYTES.with(|cell| cell.set(None));
        assert!(
            report.proof_artifact_root.is_some(),
            "with no inline budget the seal must keep the private store for path-backed evidence"
        );
        let canonical = report
            .live_transport_authority
            .as_ref()
            .and_then(LiveTransportAuthority::sealed_canonical_publication)
            .expect("sealed canonical publication")
            .0
            .clone();
        assert!(
            report_evidence_artifacts(&canonical).iter().any(|artifact| artifact
                .materialization
                .as_ref()
                .is_some_and(|materialization| materialization.materialized_path.is_some())),
            "the sealed canonical report must still reference the store"
        );
        (canonical, digest)
    }

    fn read_sidecar(output: &Path) -> serde_json::Value {
        serde_json::from_slice(
            &fs::read(output.join(REPORT_EVIDENCE_BUNDLE_FILE)).expect("read evidence-bundle.json"),
        )
        .expect("evidence-bundle.json is JSON")
    }

    fn store_entry(output: &Path, digest: &str) -> PathBuf {
        output.join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256").join(digest)
    }

    /// The challenge's correction: `total_proved == 0` and `evidence_defects`
    /// are produced by EVERY reload (saved reports never carry authority), so
    /// they cannot tell an omitted artifact from a persisted one. Only
    /// `structural_evidence_defects` moves, and only against a complete
    /// baseline of zero.
    #[test]
    fn store_cap_keeps_the_report_and_records_the_omission_instead_of_failing() {
        let source = tempfile::tempdir().expect("source root");
        let (canonical, digest) = sealed_store_backed_canonical_report(source.path());

        // Baseline: complete bundle (copy, no link) reloads with NO structural defect.
        let complete = tempfile::tempdir().expect("complete output");
        {
            let _policy = artifact_store_policy(MAX_REPORT_ARTIFACT_STORE_BYTES, false);
            let status = write_report_artifacts_from_root(
                &canonical,
                complete.path(),
                "<html>trust</html>",
                Some(source.path()),
                None,
                None,
            )
            .expect("complete bundle");
            assert!(status.complete);
            assert_eq!((status.copied_artifacts, status.omitted_artifacts), (1, 0));
        }
        assert!(store_entry(complete.path(), &digest.value).is_file());
        assert_eq!(read_sidecar(complete.path())["complete"], true);
        let baseline = crate::saved_report::load_report(&complete.path().join("report.json"))
            .expect("reload complete bundle");
        assert_eq!(
            baseline.sanitization.structural_evidence_defects, 0,
            "{:?}",
            baseline.report.functions[0].obligations[0].outcome
        );

        // Capped: the copy cap is below the one artifact.
        let capped = tempfile::tempdir().expect("capped output");
        let status = {
            let _policy = artifact_store_policy(0, false);
            write_report_artifacts_from_root(
                &canonical,
                capped.path(),
                "<html>trust</html>",
                Some(source.path()),
                None,
                None,
            )
            .expect("the store cap must no longer fail the report transaction")
        };
        assert!(!status.complete);
        assert_eq!(status.omitted_artifacts, 1);
        assert_eq!(status.omitted_proved_or_runtime_checked_rows, 1);
        for name in ["report.json", "report.ndjson", "report.html", REPORT_EVIDENCE_BUNDLE_FILE] {
            assert!(capped.path().join(name).is_file(), "{name} must be written");
        }
        assert!(!store_entry(capped.path(), &digest.value).exists(), "omitted, not persisted");

        let sidecar = read_sidecar(capped.path());
        assert_eq!(sidecar["schema"], REPORT_EVIDENCE_BUNDLE_SCHEMA);
        assert_eq!(sidecar["complete"], false);
        assert_eq!(sidecar["omitted_artifacts"], 1);
        assert_eq!(sidecar["copy_cap_bytes"], 0);
        assert_eq!(sidecar["unsafe_memory_wrapper"], "not_requested");
        assert_eq!(sidecar["omitted"][0]["digest_sha256"], digest.value.as_str());
        assert_eq!(sidecar["omitted"][0]["rows"][0]["outcome"], "proved");
        assert_eq!(
            sidecar["proof_report_hash"],
            format!(
                "sha256:{}",
                file_sha256_hex(&capped.path().join("report.json")).expect("hash report")
            ),
            "the sidecar must be bound to the exact report bytes it describes"
        );

        let reloaded = crate::saved_report::load_report(&capped.path().join("report.json"))
            .expect("an incomplete bundle still reloads (fail-closed, as diagnostics)");
        assert!(
            reloaded.sanitization.structural_evidence_defects >= 1,
            "the omitted proved-row artifact must surface as a structural defect on reload"
        );
        assert_eq!(reloaded.report.summary.total_proved, 0);

        let lines = evidence_bundle_incomplete_lines(&status, capped.path());
        assert!(lines.iter().any(|line| line.contains("INCOMPLETE")), "{lines:?}");
        assert!(lines.iter().any(|line| line.contains(REPORT_EVIDENCE_BUNDLE_FILE)), "{lines:?}");
        assert!(
            evidence_bundle_incomplete_lines(&EvidenceBundleStatus::empty(0), capped.path())
                .is_empty()
        );
    }

    /// Proved-row evidence is persisted FIRST, and an omitted artifact behind
    /// an UNKNOWN row — which leaves no reload trace at all — is in the record.
    #[test]
    fn store_cap_persists_proved_rows_first_and_records_omitted_unknown_rows() {
        let source = tempfile::tempdir().expect("source root");
        let (mut canonical, proved_digest) = sealed_store_backed_canonical_report(source.path());
        let proved_len = proved_artifact_len(&canonical);
        let unknown_bytes = b"unk";
        assert!((unknown_bytes.len() as u64) < proved_len, "fixture sizes");
        let unknown_digest =
            insert_unknown_row_with_own_artifact(&mut canonical, source.path(), unknown_bytes);
        assert!(
            matches!(
                canonical.functions[0].obligations[0].outcome,
                ObligationOutcome::Unknown { .. }
            ),
            "the unknown row comes FIRST in report order, so report order alone would persist it"
        );

        // Exactly the proved artifact fits: the boundary is inclusive.
        let output = tempfile::tempdir().expect("output");
        let status = {
            let _policy = artifact_store_policy(proved_len, false);
            write_report_artifacts_from_root(
                &canonical,
                output.path(),
                "<html>trust</html>",
                Some(source.path()),
                None,
                None,
            )
            .expect("capped bundle")
        };
        assert!(store_entry(output.path(), &proved_digest.value).is_file());
        assert!(!store_entry(output.path(), &unknown_digest).exists());
        assert_eq!(status.copied_bytes, proved_len);
        assert_eq!(status.omitted_proved_or_runtime_checked_rows, 0);
        let sidecar = read_sidecar(output.path());
        assert_eq!(sidecar["complete"], false);
        assert_eq!(sidecar["omitted"].as_array().map(Vec::len), Some(1));
        assert_eq!(sidecar["omitted"][0]["digest_sha256"], unknown_digest.as_str());
        assert_eq!(sidecar["omitted"][0]["rows"][0]["outcome"], "unknown");
        assert_eq!(sidecar["omitted"][0]["rows"][0]["function"], "crate::unknown_row");
        let reloaded =
            crate::saved_report::load_report(&output.path().join("report.json")).expect("reload");
        assert_eq!(
            reloaded.sanitization.structural_evidence_defects, 0,
            "the unknown row's omission leaves no reload trace; only the sidecar records it"
        );

        // One byte under: the proved artifact is omitted, and the walk CONTINUES,
        // so the smaller unknown-row artifact still fits.
        let under = tempfile::tempdir().expect("output");
        let status = {
            let _policy = artifact_store_policy(proved_len - 1, false);
            write_report_artifacts_from_root(
                &canonical,
                under.path(),
                "<html>trust</html>",
                Some(source.path()),
                None,
                None,
            )
            .expect("capped bundle")
        };
        assert!(!store_entry(under.path(), &proved_digest.value).exists());
        assert!(store_entry(under.path(), &unknown_digest).is_file());
        assert_eq!(status.omitted_proved_or_runtime_checked_rows, 1);
        assert_eq!(status.omitted[0].digest_sha256, proved_digest.value);
    }

    /// The duplicate re-read is gone; its byte_len check is not.
    #[test]
    fn duplicate_artifact_occurrences_must_agree_on_byte_len_and_join_the_omission_record() {
        let source = tempfile::tempdir().expect("source root");
        let (mut canonical, digest) = sealed_store_backed_canonical_report(source.path());
        let mut duplicate = canonical.functions[0].clone();
        duplicate.function = "crate::duplicate_row".to_string();
        canonical.functions.push(duplicate);

        let output = tempfile::tempdir().expect("output");
        let status = {
            let _policy = artifact_store_policy(0, false);
            write_report_artifacts_from_root(
                &canonical,
                output.path(),
                "<html>trust</html>",
                Some(source.path()),
                None,
                None,
            )
            .expect("capped bundle")
        };
        assert_eq!(status.omitted_artifacts, 1, "omissions are unique by digest");
        assert_eq!(status.omitted[0].digest_sha256, digest.value);
        assert_eq!(status.omitted[0].rows.len(), 2, "every referencing row is recorded");
        assert_eq!(status.omitted_proved_or_runtime_checked_rows, 2);

        let mut disagreeing = canonical.clone();
        let mut obligation = disagreeing.functions[1].obligations[0].clone();
        for artifact in path_backed_artifacts_mut(&mut obligation) {
            artifact.materialization.as_mut().expect("materialization").byte_len += 1;
        }
        disagreeing.functions[1].obligations[0] = obligation;
        let output = tempfile::tempdir().expect("output");
        let _policy = artifact_store_policy(MAX_REPORT_ARTIFACT_STORE_BYTES, false);
        let error = write_report_artifacts_from_root(
            &disagreeing,
            output.path(),
            "<html>trust</html>",
            Some(source.path()),
            None,
            None,
        )
        .expect_err("a duplicate declaring a different byte_len must be refused");
        assert!(error.to_string().contains("earlier occurrence"), "{error}");
        assert!(!output.path().join("report.json").exists());
    }

    /// Review finding (2026-10-01): `omitted_proved_or_runtime_checked_rows`
    /// counted row-artifact PAIRS. One proved row whose two DISTINCT artifacts
    /// are both omitted is one row.
    #[test]
    fn one_proved_row_with_two_omitted_artifacts_counts_as_one_row() {
        let source = tempfile::tempdir().expect("source root");
        let (mut canonical, first_digest) = sealed_store_backed_canonical_report(source.path());
        let second_bytes = b"second distinct artifact of the same proved row";
        let second_digest = trust_types::digest::lowercase_hex(&Sha256::digest(second_bytes));
        let store =
            source.path().join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256");
        fs::write(store.join(&second_digest), second_bytes).expect("write second artifact");
        {
            let obligation = &mut canonical.functions[0].obligations[0];
            assert!(matches!(obligation.outcome, ObligationOutcome::Proved { .. }));
            let mut extra = path_backed_artifacts_mut(obligation)[0].clone();
            extra.digest.as_mut().expect("digest").value = second_digest.clone();
            let materialization = extra.materialization.as_mut().expect("materialization");
            materialization.byte_len = second_bytes.len() as u64;
            materialization.materialized_path = Some(format!(
                "{}/sha256/{second_digest}",
                trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY
            ));
            if let Some(proof) = obligation.proof_evidence.as_mut() {
                proof.artifacts.push(extra);
            } else {
                obligation
                    .transport_evidence
                    .as_mut()
                    .and_then(|transport| transport.proof_evidence.as_mut())
                    .expect("proof evidence to carry the second artifact")
                    .artifacts
                    .push(extra);
            }
        }

        let output = tempfile::tempdir().expect("output");
        let status = {
            let _policy = artifact_store_policy(0, false);
            write_report_artifacts_from_root(
                &canonical,
                output.path(),
                "<html>trust</html>",
                Some(source.path()),
                None,
                None,
            )
            .expect("capped bundle")
        };
        assert_eq!(status.omitted_artifacts, 2, "two distinct digests omitted");
        let omitted: Vec<&str> =
            status.omitted.iter().map(|artifact| artifact.digest_sha256.as_str()).collect();
        assert!(omitted.contains(&first_digest.value.as_str()), "{omitted:?}");
        assert!(omitted.contains(&second_digest.as_str()), "{omitted:?}");
        for artifact in &status.omitted {
            assert_eq!(artifact.rows.len(), 1, "each omission names its one row once");
        }
        assert_eq!(
            status.omitted_proved_or_runtime_checked_rows, 1,
            "one proved row lost evidence, however many of its artifacts were omitted"
        );
        assert_eq!(read_sidecar(output.path())["omitted_proved_or_runtime_checked_rows"], 1);
    }

    /// Review finding (2026-10-01): a run that DEMANDS a complete bundle exits
    /// 2 over an incomplete one, so its machine stdout must not carry the
    /// sealed, success-shaped bytes. The advisory ramp keeps the exact sealed
    /// bytes on stdout, and a complete bundle publishes them on every lane.
    #[test]
    fn machine_stdout_is_withheld_only_when_a_required_bundle_is_incomplete() {
        let source = tempfile::tempdir().expect("source root");
        test_hooks::INLINE_BUDGET_BYTES.with(|cell| cell.set(Some(0)));
        let (report, _digest) = sealed_path_backed_native_report(source.path());
        test_hooks::INLINE_BUDGET_BYTES.with(|cell| cell.set(None));
        assert!(report.proof_artifact_root.is_some());
        let sealed_bytes = report
            .live_transport_authority
            .as_ref()
            .and_then(LiveTransportAuthority::sealed_canonical_publication)
            .expect("sealed canonical publication")
            .1
            .to_vec();
        let mut expected_json = sealed_bytes.clone();
        expected_json.push(b'\n');

        let render = |format: OutputFormat, cap: u64, required: bool| {
            let _policy = artifact_store_policy(cap, false);
            let output = tempfile::tempdir().expect("output");
            let mut stdout = Vec::new();
            let status = report
                .render_published(
                    format,
                    Some(output.path().to_str().expect("utf-8")),
                    None,
                    required,
                    &mut stdout,
                )
                .expect("render publishes")
                .expect("bundle status");
            assert_eq!(
                fs::read(output.path().join("report.json")).expect("report.json saved"),
                sealed_bytes,
                "the sealed report is saved whatever stdout carries"
            );
            (status.complete, stdout)
        };

        // Required + incomplete: withheld, for both machine formats.
        let (complete, stdout) = render(OutputFormat::Json, 0, true);
        assert!(!complete);
        assert!(stdout.is_empty(), "JSON stdout must be withheld: {} bytes", stdout.len());
        let (complete, stdout) = render(OutputFormat::Html, 0, true);
        assert!(!complete);
        assert!(stdout.is_empty(), "HTML stdout must be withheld: {} bytes", stdout.len());

        // Advisory (not required) + incomplete: the exact sealed bytes.
        let (complete, stdout) = render(OutputFormat::Json, 0, false);
        assert!(!complete);
        assert_eq!(stdout, expected_json);

        // Required + complete: the exact sealed bytes.
        let (complete, stdout) = render(OutputFormat::Json, MAX_REPORT_ARTIFACT_STORE_BYTES, true);
        assert!(complete);
        assert_eq!(stdout, expected_json);
        let (complete, stdout) = render(OutputFormat::Html, MAX_REPORT_ARTIFACT_STORE_BYTES, true);
        assert!(complete);
        assert!(!stdout.is_empty());
    }

    /// On one filesystem the bundle hard-links the private store's file: no
    /// second copy, not charged to the copy cap, still re-hashed.
    #[cfg(unix)]
    #[test]
    fn same_filesystem_bundle_links_instead_of_copying_and_is_not_charged() {
        use std::os::unix::fs::MetadataExt as _;

        let source = tempfile::tempdir().expect("source root");
        let (canonical, digest) = sealed_store_backed_canonical_report(source.path());
        let output = tempfile::tempdir_in(source.path()).expect("output on the same filesystem");
        let status = {
            let _policy = artifact_store_policy(0, true);
            write_report_artifacts_from_root(
                &canonical,
                output.path(),
                "<html>trust</html>",
                Some(source.path()),
                None,
                None,
            )
            .expect("linked bundle")
        };
        assert!(status.complete, "a linked artifact costs no copy, so a zero cap omits nothing");
        assert_eq!((status.linked_artifacts, status.copied_bytes), (1, 0));
        let linked = fs::metadata(store_entry(output.path(), &digest.value)).expect("linked");
        let original = fs::metadata(store_entry(source.path(), &digest.value)).expect("source");
        assert_eq!(linked.ino(), original.ino(), "persisted by hard link");
        let reloaded =
            crate::saved_report::load_report(&output.path().join("report.json")).expect("reload");
        assert_eq!(reloaded.sanitization.structural_evidence_defects, 0);

        // A tampered private-store file is refused through the link, as a copy was.
        let tampered_source = tempfile::tempdir().expect("source root");
        let (canonical, digest) = sealed_store_backed_canonical_report(tampered_source.path());
        let entry = store_entry(tampered_source.path(), &digest.value);
        let mut bytes = fs::read(&entry).expect("read artifact");
        bytes[0] ^= 1;
        fs::write(&entry, bytes).expect("tamper artifact");
        let output = tempfile::tempdir_in(tampered_source.path()).expect("output");
        let _policy = artifact_store_policy(MAX_REPORT_ARTIFACT_STORE_BYTES, true);
        write_report_artifacts_from_root(
            &canonical,
            output.path(),
            "<html>trust</html>",
            Some(tampered_source.path()),
            None,
            None,
        )
        .expect_err("tampered evidence stays a hard failure");
        assert!(!output.path().join("report.json").exists());
    }

    /// The live path end to end: the seal keeps the artifact in the private
    /// store, `render` publishes the verdict and the bundle, and an
    /// `--unsafe-memory` wrapper is WITHHELD over the incomplete bundle while
    /// it is written over a complete one.
    #[test]
    fn render_publishes_over_a_capped_store_and_withholds_the_unsafe_memory_wrapper() {
        let _hooks = artifact_store_policy(MAX_REPORT_ARTIFACT_STORE_BYTES, false);
        test_hooks::INLINE_BUDGET_BYTES.with(|cell| cell.set(Some(0)));
        let source = tempfile::tempdir().expect("source root");
        let (report, digest) = sealed_path_backed_native_report(source.path());
        assert!(
            report.proof_artifact_root.is_some(),
            "with no inline budget the seal must keep the private store for path-backed evidence"
        );
        let repo = clean_git_repo("blocker4-capped-unsafe-memory");
        let request = UnsafeMemoryReportRequest::new(repo.clone());

        // Control: a complete bundle carries the wrapper. (Outside the repo, so
        // the second render still sees a clean tree.)
        let output = tempfile::tempdir().expect("report output");
        let complete_dir = output.path().to_path_buf();
        let status = report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(complete_dir.to_str().expect("utf-8")),
                Some(&request),
            )
            .expect("complete bundle renders")
            .expect("report_dir yields a bundle status");
        assert!(status.complete);
        assert!(store_entry(&complete_dir, &digest.value).is_file());
        assert!(complete_dir.join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE).is_file());
        assert_eq!(read_sidecar(&complete_dir)["unsafe_memory_wrapper"], "written");

        // Capped: the verdict still renders (Ok), the report is written, the
        // wrapper is not, and the status says why.
        test_hooks::ARTIFACT_STORE_POLICY.with(|cell| {
            cell.set(Some(ArtifactStorePolicy {
                copy_cap_bytes: 0,
                link_from_private_store: false,
            }));
        });
        // Same directory: the control run's wrapper is now the stale one.
        let capped_dir = complete_dir.clone();
        let status = report
            .render_with_unsafe_memory_report(
                OutputFormat::Terminal,
                Some(capped_dir.to_str().expect("utf-8")),
                Some(&request),
            )
            .expect("an over-cap store must not discard the verdict")
            .expect("report_dir yields a bundle status");
        assert!(!status.complete);
        assert!(capped_dir.join("report.json").is_file());
        assert!(!store_entry(&capped_dir, &digest.value).exists());
        assert!(
            !capped_dir.join(PROOF_UNSAFE_MEMORY_WRAPPER_FILE).exists(),
            "neither a new nor a stale unsafe-memory wrapper may stand over an incomplete bundle"
        );
        let sidecar = read_sidecar(&capped_dir);
        assert_eq!(sidecar["unsafe_memory_wrapper"], "withheld_incomplete_bundle");
        assert_eq!(sidecar["complete"], false);

        let _ = fs::remove_dir_all(repo);
    }
    include!("publication_stop_tests.rs");
}
