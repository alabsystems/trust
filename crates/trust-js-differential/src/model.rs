// Data model for the TrustJS Channel-A harness: the corpus pin
// (trust.js262.corpus-pin.v1), the S0 slice manifest, the js262 ledgers
// (baseline / test-exceptions / divergence-audit — shapes cloned from
// crates/trust-upstream-compat/src/model.rs discipline: deny_unknown_fields,
// snake_case enums, schema_version fields), the calibration scorecard
// (trust.js262.scorecard.v1), and the adopted-execution evidence report.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Corpus pin — trust.js262.corpus-pin.v1
// ---------------------------------------------------------------------------

pub const CORPUS_PIN_SCHEMA: &str = "trust.js262.corpus-pin.v1";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CorpusPin {
    /// Always `trust.js262.corpus-pin.v1`.
    pub schema: String,
    /// Pin creation date, `YYYY-MM-DD`.
    pub date: String,
    /// Upstream provenance.
    pub upstream: PinUpstream,
    /// The exact corpus git commit.
    pub git_commit_hash: String,
    /// Every file under `harness/` ending `.js`, sorted bytewise by
    /// `relative_path`.
    pub payloads: Vec<PinPayload>,
    /// sha256 over UTF-8 concat of `relative_path + "\n" + sha256 + "\n"`
    /// per payload in listed order.
    pub manifest_hash: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PinUpstream {
    pub repo: String,
    pub revision: String,
    pub snapshot_date: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PinPayload {
    /// Corpus-relative path with forward slashes, e.g. `harness/assert.js`.
    pub relative_path: String,
    pub sha256: String,
}

// ---------------------------------------------------------------------------
// S0 slice manifest — trust.js262.slice.v1
// ---------------------------------------------------------------------------

pub const SLICE_SCHEMA: &str = "trust.js262.slice.v1";

/// The payload-external committed S0.toml shape (schema_version + [corpus] +
/// [rules] + [derived], no embedded test list): the slice is re-derived from
/// the pinned corpus and checked against [derived]; [rules] must match the
/// canonical selection constants exactly. Unknown fields tolerated.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct ExternalSliceManifest {
    pub schema_version: String,
    pub id: String,
    pub corpus: ExternalSliceCorpus,
    pub rules: ExternalSliceRules,
    pub derived: ExternalSliceDerived,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct ExternalSliceCorpus {
    pub revision: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct ExternalSliceRules {
    pub include_prefixes: Vec<String>,
    pub exclude_prefixes: Vec<String>,
    pub exclude_suffixes: Vec<String>,
    /// Flags a case MUST carry to be selected. Absent (S0) => empty; the
    /// S-async slice declares `["async"]`. Kept optional so the frozen S0.toml
    /// (which omits it) keeps parsing unchanged.
    #[serde(default)]
    pub require_flags: Vec<String>,
    pub exclude_flags: Vec<String>,
    pub exclude_content_substrings: Vec<String>,
    pub exclude_features: Vec<String>,
    pub exclude_feature_substrings: Vec<String>,
    pub exclude_proposal_features_from: String,
    pub exclude_include_content_substrings: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct ExternalSliceDerived {
    pub count: u64,
    pub list_sha256: String,
}

/// The embedded slice-manifest shape written by `slice-derive --out` when the
/// full path list is wanted inline. Unknown fields are tolerated (the
/// selection contract is enforced by re-derivation, not field-set identity).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SliceManifest {
    /// Always `trust.js262.slice.v1`.
    pub schema: String,
    /// Slice identifier, `S0`.
    pub slice: String,
    /// Corpus git commit the slice was derived from.
    pub corpus_revision: String,
    /// Derivation date, `YYYY-MM-DD`.
    pub derived_on: String,
    /// Number of selected tests (== `tests.len()`).
    pub count: u64,
    /// sha256 over UTF-8 concat of `path + "\n"` per selected path in sorted
    /// order.
    pub list_sha256: String,
    /// sha256 of the canonical S0 selection-rules text.
    pub rules_sha256: String,
    /// All selected corpus-relative paths, sorted bytewise ascending.
    pub tests: Vec<String>,
}

// ---------------------------------------------------------------------------
// Ledgers — tests/js262/{baseline,test-exceptions,divergence-audit}.toml
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Js262Baseline {
    pub schema_version: String,
    pub id: String,
    pub upstream: Js262UpstreamSnapshot,
    pub local: Js262LocalSnapshot,
    pub entries: Vec<Js262BaselineEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Js262UpstreamSnapshot {
    /// Always `test262`.
    pub channel: String,
    pub revision: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub snapshot_date: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Js262LocalSnapshot {
    pub revision: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub branch: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub workspace: Option<String>,
}

/// One baseline claim. `surface` is a free token (canonical values:
/// engine_node | engine_bun | engine_sem | harness | js262 | other); the
/// committed seed baseline also carries the upstream-compat artifact and
/// expectation fields, so they are first-class here.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Js262BaselineEntry {
    pub id: String,
    pub title: String,
    pub surface: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub upstream_artifact: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub local_artifact: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expectation: Option<Js262Expectation>,
    pub status: Js262BaselineStatus,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub labels: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Js262Expectation {
    pub upstream_behavior: String,
    pub local_behavior: String,
    pub compatibility_rule: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Js262BaselineStatus {
    Compatible,
    Diverged,
    MissingLocal,
    MissingUpstream,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Js262TestExceptionLedger {
    pub schema_version: String,
    pub exceptions: Vec<Js262TestException>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Js262TestException {
    pub id: String,
    pub test_id: String,
    pub suite: String,
    pub path: String,
    pub kind: Js262TestExceptionKind,
    pub status: Js262ExceptionStatus,
    pub owner: String,
    pub reason: String,
    pub issue: String,
    /// `YYYY-MM-DD`.
    pub reviewed_on: String,
    /// `YYYY-MM-DD`; must be after `reviewed_on` and after the validation
    /// date for the exception to remain active.
    pub expires_on: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub allowed_patterns: Vec<String>,
}

/// Exception kinds: the upstream-compat five plus the js262 ledger header's
/// documented calibration kinds (trace_divergence / harness_limit /
/// engine_timeout).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Js262TestExceptionKind {
    ExpectedFail,
    ExpectedSkip,
    ChangedDiagnostic,
    IntentionalDivergence,
    EnvironmentalSkip,
    TraceDivergence,
    HarnessLimit,
    EngineTimeout,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Js262ExceptionStatus {
    Active,
    Expired,
    /// `retired` is accepted as an input alias (js262 ledger header vocab).
    #[serde(alias = "retired")]
    Resolved,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Js262DivergenceAudit {
    pub schema_version: String,
    pub entries: Vec<Js262AuditEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Js262AuditEntry {
    pub id: String,
    /// Corpus-relative test path.
    pub path: String,
    /// `bare` | `strict` | `raw` (informational; the fingerprint already
    /// binds the mode).
    pub mode: String,
    /// Which differential lane the entry waives: the M0 trace lane
    /// (default, `trace`) or the M1 parse-verdict lane (`parse`). The serde
    /// default keeps every pre-M1 entry valid unchanged; each lane consumes
    /// only its own entries.
    #[serde(default, skip_serializing_if = "js262_audit_head_is_default")]
    pub head: Js262AuditHead,
    /// First 16 hex of sha256(path + "|" + mode + "|" + explain) for the
    /// trace lane; sha256(path + "|" + mode + "|" + direction) for the
    /// parse lane.
    pub fingerprint: String,
    pub classification: Js262Classification,
    pub status: Js262AuditStatus,
    pub owner: String,
    pub reason: String,
    /// Issue link; the sole accountability anchor for permanent entries.
    pub issue: String,
    /// `YYYY-MM-DD`.
    pub reviewed_on: String,
    /// Permanent-category entries (benign_host_defined / spec_bug only)
    /// carry issue links instead of expiry.
    #[serde(default)]
    pub permanent: bool,
    /// REQUIRED unless `permanent`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expires_on: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Js262Classification {
    BenignHostDefined,
    NodeBug,
    BunBug,
    SpecBug,
    /// NEVER a waiver: its presence demands a trust-js-trace projection fix.
    ProjectionTooStrong,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Js262AuditStatus {
    Active,
    /// `retired` is accepted as an input alias (js262 ledger header vocab).
    #[serde(alias = "retired")]
    Resolved,
}

/// The differential lane a divergence-audit entry belongs to.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Js262AuditHead {
    /// The M0 trace-differential lane (Node vs Bun vs sem).
    #[default]
    Trace,
    /// The M1 D1 parse-verdict lane (trust-js-parse vs node --check).
    Parse,
}

fn js262_audit_head_is_default(head: &Js262AuditHead) -> bool {
    *head == Js262AuditHead::Trace
}

// ---------------------------------------------------------------------------
// Scorecard — trust.js262.scorecard.v1
// ---------------------------------------------------------------------------

pub const SCORECARD_SCHEMA: &str = "trust.js262.scorecard.v1";

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Scorecard {
    /// Always `trust.js262.scorecard.v1`.
    pub schema: String,
    pub generated_at: String,
    /// Present (true) iff the run was truncated by `--limit`; a partial
    /// scorecard NEVER claims the gate.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub partial: Option<bool>,
    pub corpus: ScorecardCorpus,
    pub engines: ScorecardEngines,
    pub driver_sha256: String,
    pub totals: ScorecardTotals,
    pub gate: ScorecardGate,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScorecardCorpus {
    pub revision: String,
    pub slice_sha256: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScorecardEngines {
    pub node: ScorecardEngine,
    pub bun: ScorecardEngine,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScorecardEngine {
    pub path: String,
    pub version: String,
    pub sha256: String,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScorecardTotals {
    /// S0 cases attempted (post `--limit`).
    pub cases: u64,
    /// Engine-pair runs attempted (case × mandated mode; an unassemblable
    /// case counts as one failed run).
    pub runs: u64,
    pub trace_equal_runs: u64,
    pub divergent_runs: u64,
    pub divergent_cases: u64,
    pub classified_divergent_cases: u64,
    pub unclassified_divergent_cases: u64,
    /// Runs where a head failed to produce a comparable trace (spawn/timeout/
    /// parse/include faults). tool_failures == harness_errors.
    pub harness_errors: u64,
    /// Harness-error runs accounted by an ACTIVE tests/js262 test exception
    /// (visible, expiring — not hidden, not a tool failure).
    #[serde(default)]
    pub excepted_harness_errors: u64,
    pub tool_failures: u64,
    /// unclassified_divergent_cases + sem_divergent + trustjs_divergent.
    pub failed: u64,
    pub sem_cases: u64,
    pub sem_covered: u64,
    pub sem_equal: u64,
    pub sem_divergent: u64,
    pub sem_no_coverage: u64,
    /// The M1 D3 fourth head (trust-js-interp), same audit discipline as
    /// sem_*: trustjs_covered + trustjs_no_coverage == trustjs_cases must
    /// hold, and trustjs_divergent is gate-fatal (zero wrong traces).
    /// Defaults keep pre-D3 scorecards parsing.
    #[serde(default)]
    pub trustjs_cases: u64,
    #[serde(default)]
    pub trustjs_covered: u64,
    #[serde(default)]
    pub trustjs_equal: u64,
    #[serde(default)]
    pub trustjs_divergent: u64,
    #[serde(default)]
    pub trustjs_no_coverage: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ScorecardGate {
    /// trace_equal_runs / runs (runs basis).
    pub trace_equal_ratio: f64,
    /// trace_equal_ratio >= 0.999.
    pub ratio_ok: bool,
    /// unclassified_divergent_cases == 0.
    pub unclassified_ok: bool,
    /// sem_covered + sem_no_coverage == sem_cases AND sem_divergent == 0.
    pub sem_audit_ok: bool,
    /// trustjs_covered + trustjs_no_coverage == trustjs_cases AND
    /// trustjs_divergent == 0 (vacuously true when the head is off). The
    /// default keeps pre-D3 scorecards parsing: an absent field means the
    /// lane never ran, which is vacuously OK.
    #[serde(default = "audit_vacuously_ok")]
    pub trustjs_audit_ok: bool,
    /// js262 ledger validation produced zero findings.
    pub ledger_ok: bool,
    pub pass: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

fn audit_vacuously_ok() -> bool {
    true
}

/// One divergences.jsonl row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DivergenceRow {
    pub path: String,
    pub mode: String,
    pub explain: String,
    /// First 16 hex of sha256(path + "|" + mode + "|" + explain).
    pub fingerprint: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub classification: Option<Js262Classification>,
}

// ---------------------------------------------------------------------------
// Coverage-ratchet ledger — tests/js262/coverage.toml (M1 D4)
// ---------------------------------------------------------------------------

/// The coverage-ratchet ledger: per auxiliary head (sem / trustjs), covered
/// may only grow and wrong traces stay at zero. Entries are append-only; the
/// LAST entry per head is the ratchet floor. The `ratchet` subcommand checks
/// scorecards against it (`--check`) and prints proposal blocks
/// (`--propose`) — it never writes the ledger (the content is the
/// coordinator's).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CoverageLedger {
    pub schema_version: String,
    #[serde(default)]
    pub entries: Vec<CoverageEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CoverageEntry {
    pub id: String,
    /// `YYYY-MM-DD`.
    pub date: String,
    /// The scorecard the counts were read from (path or run id).
    pub scorecard: String,
    pub head: CoverageHead,
    pub cases: u64,
    pub covered: u64,
    pub equal: u64,
    pub divergent: u64,
    pub no_coverage: u64,
}

/// The auxiliary head a coverage entry ratchets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CoverageHead {
    Sem,
    Trustjs,
}

impl CoverageHead {
    pub fn as_str(self) -> &'static str {
        match self {
            CoverageHead::Sem => "sem",
            CoverageHead::Trustjs => "trustjs",
        }
    }
}

// ---------------------------------------------------------------------------
// Parse-verdict scorecard — trust.js262.parse-verdict.v1 (M1 D1)
// ---------------------------------------------------------------------------

pub const PARSE_SCORECARD_SCHEMA: &str = "trust.js262.parse-verdict.v1";

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ParseScorecard {
    /// Always `trust.js262.parse-verdict.v1`.
    pub schema: String,
    pub generated_at: String,
    /// Present (true) iff the run was truncated by `--limit`; a partial
    /// scorecard NEVER claims the gate.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub partial: Option<bool>,
    /// Corpus git revision.
    pub corpus: String,
    /// The S0 slice list sha256.
    pub slice_sha256: String,
    /// Always `trust-js-parse`.
    pub parser: String,
    /// The node --check oracle identity (path, version, binary sha256).
    pub oracle: ScorecardEngine,
    pub totals: ParseTotals,
    pub gate: ParseGate,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ParseTotals {
    /// S0 cases attempted (post `--limit`), raw-flag cases included.
    pub cases: u64,
    /// Verdict runs attempted (non-raw case × mandated mode; an unpreparable
    /// case counts as one failed run). Invariant:
    /// agree + disagree + unsupported + oracle_errors == runs.
    pub runs: u64,
    /// Verdict-level agreements (Script<->accept, EarlyError<->reject).
    pub agree: u64,
    /// ALL verdict-level disagreements, waived and unwaived.
    pub disagree: u64,
    /// Sound parser refusals (no-coverage) — counted, never a disagreement.
    pub unsupported: u64,
    /// Raw-flag runs skipped by this lane (counted, never judged).
    pub raw_skipped: u64,
    /// Tool failures: oracle spawn/classify faults and unpreparable cases.
    pub oracle_errors: u64,
    /// Oracle-error runs accounted by an ACTIVE test exception (e.g. node
    /// --check aborting on a corpus case) — visible, expiring, not a tool
    /// failure.
    #[serde(default)]
    pub excepted_oracle_errors: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ParseGate {
    /// unwaived_disagree == 0 (disagreements modulo ACTIVE head="parse"
    /// divergence-audit entries).
    pub disagree_ok: bool,
    /// Disagreements not covered by an active head="parse" audit entry.
    pub unwaived_disagree: u64,
    /// (agree + disagree) / runs — the fraction of runs the parser judged
    /// (1.0 vacuously when runs == 0).
    pub coverage_ratio: f64,
    /// disagree_ok AND zero oracle errors AND a complete (non-partial) run.
    pub pass: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

/// One parse-verdicts-divergent.jsonl row.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParseDivergenceRow {
    pub path: String,
    /// `bare` | `strict`.
    pub mode: String,
    /// `parser-accepts-oracle-rejects` | `parser-rejects-oracle-accepts`.
    pub direction: String,
    /// First 16 hex of sha256(path + "|" + mode + "|" + direction).
    pub fingerprint: String,
    /// The parser's EarlyError reason, when the parser rejected.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parser_reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub classification: Option<Js262Classification>,
}

// ---------------------------------------------------------------------------
// Evidence — trust.js262.adopted-execution-report.v1
// ---------------------------------------------------------------------------

pub const EVIDENCE_SCHEMA: &str = "trust.js262.adopted-execution-report.v1";

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceReport {
    /// Always `trust.js262.adopted-execution-report.v1`.
    pub schema: String,
    pub schema_version: String,
    pub generated_at: String,
    pub validation_date: String,
    /// `git rev-parse HEAD`, read-only; `unknown` (with a finding) if
    /// unavailable.
    pub repo_head: String,
    /// The embedded scorecard.json, verbatim.
    pub scorecard: serde_json::Value,
    pub ledgers: EvidenceLedgers,
    /// The kernel receipts minted for this run, one per certified builtin.
    ///
    /// The rest of this report is differential evidence: two engines agreed on
    /// a trace. That is the strongest thing a harness can say, and it is not a
    /// proof. These rows are the one place in the JS lane where something is
    /// PROVED — the Clean kernel re-checks that the interpreter's builtin
    /// matches a pinned transcription, cell by cell — so they are carried
    /// separately and never folded into the agreement counts.
    pub kernel_receipts: Vec<EvidenceKernelReceipt>,
    /// Computed, never hard-coded true.
    pub claims: EvidenceClaims,
    pub validation: EvidenceValidation,
}

/// One kernel-checked builtin receipt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceKernelReceipt {
    /// The builtin the receipt is about.
    pub builtin: String,
    /// The claim, verbatim from the bridge. It says "refines OUR TRANSCRIPTION
    /// of the ECMA-262 table", not "refines ECMA-262", and softening it here
    /// would be the exact overclaim the bridge refuses to make.
    pub assurance_tier: String,
    /// sha256 of the pinned transcription the interpreter was checked against.
    pub transcription_sha256: String,
    /// Whether an independent kernel re-check of the minted term passed.
    pub kernel_recheck_passed: bool,
    /// sha256 of the serialized proof term.
    pub term_sha256: String,
    /// The obligation's lineage digest.
    pub lineage_sha256: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceLedgers {
    pub active_test_exceptions: Vec<String>,
    pub active_audit_entries: Vec<String>,
    pub expired_entries: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceClaims {
    pub calibration_gate_claimed: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceValidation {
    /// `pass` | `fail`.
    pub status: String,
    pub findings: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    const BASELINE_TOML: &str = r#"
schema_version = "1"
id = "js262-baseline-m0"

[upstream]
channel = "test262"
revision = "tc39/test262:9e61c12835c5e4a3bdba93850427e6742c4f64c4"
snapshot_date = "2026-07-21"

[local]
revision = "deadbeef"
branch = "main"

[[entries]]
id = "engine-node"
title = "Node oracle head"
surface = "engine_node"
status = "compatible"
labels = ["m0"]

[[entries]]
id = "engine.bun"
title = "Bun oracle head trace calibration"
surface = "js262"
upstream_artifact = "test262 S0 slice"
local_artifact = "trust-js-differential Bun head"
status = "unknown"
labels = ["js262"]

[entries.expectation]
upstream_behavior = "traces"
local_behavior = "same traces"
compatibility_rule = "trace-equal modulo classified divergences"
"#;

    const EXCEPTIONS_TOML: &str = r#"
schema_version = "1"

[[exceptions]]
id = "exc-1"
test_id = "test/language/x.js"
suite = "js262"
path = "test/language/x.js"
kind = "expected_fail"
status = "active"
owner = "ayates"
reason = "engine divergence under triage"
issue = "https://example.invalid/issue/1"
reviewed_on = "2026-07-01"
expires_on = "2026-09-01"
allowed_patterns = ["completion: *"]
"#;

    const AUDIT_TOML: &str = r#"
schema_version = "1"

[[entries]]
id = "aud-1"
path = "test/built-ins/Date/x.js"
mode = "bare"
fingerprint = "0123456789abcdef"
classification = "benign_host_defined"
status = "active"
owner = "ayates"
reason = "host timezone repr"
issue = "https://example.invalid/issue/2"
reviewed_on = "2026-07-01"
permanent = true
"#;

    #[test]
    fn baseline_round_trip() {
        let b: Js262Baseline = toml::from_str(BASELINE_TOML).expect("parse");
        assert_eq!(b.upstream.channel, "test262");
        assert_eq!(b.entries[0].surface, "engine_node");
        assert_eq!(b.entries[1].status, Js262BaselineStatus::Unknown);
        assert!(b.entries[1].expectation.is_some());
        let s = toml::to_string(&b).expect("serialize");
        let b2: Js262Baseline = toml::from_str(&s).expect("reparse");
        assert_eq!(b, b2);
    }

    #[test]
    fn retired_alias_accepted() {
        let src = EXCEPTIONS_TOML.replace("status = \"active\"", "status = \"retired\"");
        let l: Js262TestExceptionLedger = toml::from_str(&src).expect("parse");
        assert_eq!(l.exceptions[0].status, Js262ExceptionStatus::Resolved);
    }

    #[test]
    fn exceptions_round_trip() {
        let l: Js262TestExceptionLedger = toml::from_str(EXCEPTIONS_TOML).expect("parse");
        assert_eq!(l.exceptions.len(), 1);
        assert_eq!(l.exceptions[0].kind, Js262TestExceptionKind::ExpectedFail);
        assert_eq!(l.exceptions[0].status, Js262ExceptionStatus::Active);
        let s = toml::to_string(&l).expect("serialize");
        let l2: Js262TestExceptionLedger = toml::from_str(&s).expect("reparse");
        assert_eq!(l, l2);
    }

    #[test]
    fn audit_round_trip_and_defaults() {
        let a: Js262DivergenceAudit = toml::from_str(AUDIT_TOML).expect("parse");
        assert!(a.entries[0].permanent);
        assert_eq!(a.entries[0].expires_on, None);
        assert_eq!(a.entries[0].classification, Js262Classification::BenignHostDefined);
        let s = toml::to_string(&a).expect("serialize");
        let a2: Js262DivergenceAudit = toml::from_str(&s).expect("reparse");
        assert_eq!(a, a2);
    }

    #[test]
    fn audit_head_defaults_to_trace_and_parses_parse() {
        // An entry WITHOUT `head` (every pre-M1 entry) defaults to trace.
        let a: Js262DivergenceAudit = toml::from_str(AUDIT_TOML).expect("parse");
        assert_eq!(a.entries[0].head, Js262AuditHead::Trace);
        // The default head is not serialized: pre-M1 ledgers round-trip
        // without gaining a head key.
        let s = toml::to_string(&a).expect("serialize");
        assert!(!s.contains("head"), "default head must not serialize: {s}");

        // head = "parse" parses, round-trips, and survives re-serialization.
        let src = AUDIT_TOML.replace("mode = \"bare\"", "mode = \"bare\"\nhead = \"parse\"");
        let p: Js262DivergenceAudit = toml::from_str(&src).expect("parse head=parse");
        assert_eq!(p.entries[0].head, Js262AuditHead::Parse);
        let s = toml::to_string(&p).expect("serialize");
        assert!(s.contains("head = \"parse\""));
        let p2: Js262DivergenceAudit = toml::from_str(&s).expect("reparse");
        assert_eq!(p, p2);

        // An unknown head value is a parse error (fail-closed), and head
        // stays inside the deny_unknown_fields perimeter.
        let bad = AUDIT_TOML.replace("mode = \"bare\"", "mode = \"bare\"\nhead = \"tracee\"");
        assert!(toml::from_str::<Js262DivergenceAudit>(&bad).is_err());
    }

    #[test]
    fn committed_divergence_audit_still_parses_with_head_extension() {
        // The head extension must keep the committed ledger parsing: M0-era
        // entries (no head key) default to the trace lane, and the M1
        // parse-verdict entries carry head = "parse" explicitly.
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/js262/divergence-audit.toml");
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let audit: Js262DivergenceAudit = toml::from_str(&text)
            .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
        assert!(!audit.entries.is_empty());
        assert!(
            audit.entries.iter().any(|e| e.head == Js262AuditHead::Trace),
            "the M0 trace-lane entries must remain"
        );
        assert!(
            audit.entries.iter().any(|e| e.head == Js262AuditHead::Parse),
            "the M1 parse-lane entries must be present"
        );
        // Semantic round-trip: trace-lane entries never gain a head key on
        // serialize; parse-lane entries keep theirs.
        let s = toml::to_string(&audit).expect("serialize");
        let back: Js262DivergenceAudit = toml::from_str(&s).expect("reparse");
        assert_eq!(audit, back);
        let head_count = s.matches("\nhead").count();
        let parse_count =
            audit.entries.iter().filter(|e| e.head == Js262AuditHead::Parse).count();
        assert_eq!(head_count, parse_count, "head keys must match parse-lane entries exactly");
    }

    #[test]
    fn parse_scorecard_round_trip() {
        let s = ParseScorecard {
            schema: PARSE_SCORECARD_SCHEMA.to_string(),
            generated_at: "2026-07-21T00:00:00Z".to_string(),
            partial: Some(true),
            corpus: "cafe".to_string(),
            slice_sha256: "00".to_string(),
            parser: "trust-js-parse".to_string(),
            oracle: ScorecardEngine { path: "n".into(), version: "v24".into(), sha256: "0".into() },
            totals: ParseTotals { cases: 2, runs: 3, unsupported: 3, ..Default::default() },
            gate: ParseGate {
                disagree_ok: true,
                unwaived_disagree: 0,
                coverage_ratio: 0.0,
                pass: false,
                reason: Some("partial".into()),
            },
        };
        let json = serde_json::to_string_pretty(&s).unwrap();
        let back: ParseScorecard = serde_json::from_str(&json).unwrap();
        assert_eq!(back.schema, PARSE_SCORECARD_SCHEMA);
        assert_eq!(back.totals, s.totals);
        assert_eq!(back.gate.unwaived_disagree, 0);
        // deny_unknown_fields keeps the schema honest.
        let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
        v.as_object_mut().unwrap().insert("surprise".into(), serde_json::json!(1));
        assert!(serde_json::from_value::<ParseScorecard>(v).is_err());
    }

    #[test]
    fn deny_unknown_fields_rejects() {
        let bad = format!("{BASELINE_TOML}\nsurprise = 1\n");
        assert!(toml::from_str::<Js262Baseline>(&bad).is_err());
        let bad = EXCEPTIONS_TOML.replace("allowed_patterns", "allowed_patterns_typo");
        assert!(toml::from_str::<Js262TestExceptionLedger>(&bad).is_err());
        let bad = AUDIT_TOML.replace("permanent = true", "permanant = true");
        assert!(toml::from_str::<Js262DivergenceAudit>(&bad).is_err());
    }

    const COVERAGE_TOML: &str = r#"
schema_version = "1"

[[entries]]
id = "cov-trustjs-2026-07-21"
date = "2026-07-21"
scorecard = "build/js262/calibration/scorecard.json"
head = "trustjs"
cases = 100
covered = 40
equal = 40
divergent = 0
no_coverage = 60
"#;

    #[test]
    fn coverage_ledger_round_trip_and_deny_unknown() {
        let l: CoverageLedger = toml::from_str(COVERAGE_TOML).expect("parse");
        assert_eq!(l.entries.len(), 1);
        assert_eq!(l.entries[0].head, CoverageHead::Trustjs);
        assert_eq!(l.entries[0].covered, 40);
        let s = toml::to_string(&l).expect("serialize");
        assert!(s.contains("head = \"trustjs\""));
        let l2: CoverageLedger = toml::from_str(&s).expect("reparse");
        assert_eq!(l, l2);
        // head = "sem" is the other valid lane; anything else fails closed.
        let sem = COVERAGE_TOML.replace("head = \"trustjs\"", "head = \"sem\"");
        assert_eq!(
            toml::from_str::<CoverageLedger>(&sem).expect("sem").entries[0].head,
            CoverageHead::Sem
        );
        let bad = COVERAGE_TOML.replace("head = \"trustjs\"", "head = \"interp\"");
        assert!(toml::from_str::<CoverageLedger>(&bad).is_err());
        let bad = format!("{COVERAGE_TOML}\nsurprise = 1\n");
        assert!(toml::from_str::<CoverageLedger>(&bad).is_err());
        let bad = COVERAGE_TOML.replace("no_coverage = 60", "no_coverage = 60\nowner = \"x\"");
        assert!(toml::from_str::<CoverageLedger>(&bad).is_err());
        // An empty ledger (header only) parses: entries defaults to [].
        let empty: CoverageLedger = toml::from_str("schema_version = \"1\"\n").expect("empty");
        assert!(empty.entries.is_empty());
    }

    #[test]
    fn pre_d3_scorecard_parses_with_trustjs_defaults() {
        // A pre-D3 scorecard has neither trustjs_* totals nor
        // gate.trustjs_audit_ok; it must keep parsing, with the absent lane
        // read as never-ran (zero counters, vacuously-OK audit).
        let json = serde_json::json!({
            "schema": SCORECARD_SCHEMA,
            "generated_at": "2026-07-20T00:00:00Z",
            "corpus": {"revision": "cafe", "slice_sha256": "00"},
            "engines": {
                "node": {"path": "n", "version": "v", "sha256": "0"},
                "bun": {"path": "b", "version": "v", "sha256": "0"}
            },
            "driver_sha256": "d",
            "totals": {
                "cases": 1, "runs": 2, "trace_equal_runs": 2, "divergent_runs": 0,
                "divergent_cases": 0, "classified_divergent_cases": 0,
                "unclassified_divergent_cases": 0, "harness_errors": 0,
                "tool_failures": 0, "failed": 0, "sem_cases": 2, "sem_covered": 1,
                "sem_equal": 1, "sem_divergent": 0, "sem_no_coverage": 1
            },
            "gate": {
                "trace_equal_ratio": 1.0, "ratio_ok": true, "unclassified_ok": true,
                "sem_audit_ok": true, "ledger_ok": true, "pass": true
            }
        });
        let s: Scorecard = serde_json::from_value(json).expect("pre-D3 scorecard parses");
        assert_eq!(s.totals.trustjs_cases, 0);
        assert_eq!(s.totals.trustjs_covered, 0);
        assert_eq!(s.totals.trustjs_divergent, 0);
        assert!(s.gate.trustjs_audit_ok, "absent lane is vacuously OK");
    }

    #[test]
    fn corpus_pin_deny_unknown() {
        let good = serde_json::json!({
            "schema": CORPUS_PIN_SCHEMA,
            "date": "2026-07-21",
            "upstream": {
                "repo": "https://github.com/tc39/test262.git",
                "revision": "tc39/test262:9e61c12835c5e4a3bdba93850427e6742c4f64c4",
                "snapshot_date": "2026-07-21"
            },
            "git_commit_hash": "9e61c12835c5e4a3bdba93850427e6742c4f64c4",
            "payloads": [{"relative_path": "harness/assert.js", "sha256": "00"}],
            "manifest_hash": "11"
        });
        let pin: CorpusPin = serde_json::from_value(good.clone()).expect("parse");
        assert_eq!(pin.payloads.len(), 1);
        let mut bad = good;
        bad.as_object_mut().unwrap().insert("extra".into(), serde_json::json!(1));
        assert!(serde_json::from_value::<CorpusPin>(bad).is_err());
    }
}
