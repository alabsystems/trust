//! Data model for upstream compatibility accounting.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// Compatibility baseline for a pair of upstream and local snapshots.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompatibilityBaseline {
    /// Version of this accounting schema.
    pub schema_version: String,
    /// Stable baseline identifier used by result summaries and ledgers.
    pub id: String,
    /// Upstream Rust snapshot the baseline was compared against.
    pub upstream: UpstreamSnapshot,
    /// Local Trust snapshot that was compared.
    pub local: LocalSnapshot,
    /// Per-surface compatibility entries.
    pub entries: Vec<BaselineEntry>,
}

/// Upstream Rust revision information.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UpstreamSnapshot {
    /// Upstream channel or branch name, such as `nightly` or `stable`.
    pub channel: String,
    /// Upstream git revision, release tag, or other immutable revision label.
    pub revision: String,
    /// Optional source date in `YYYY-MM-DD` form.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub snapshot_date: Option<String>,
}

/// Local Trust revision information.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalSnapshot {
    /// Local git revision, release tag, or other immutable revision label.
    pub revision: String,
    /// Optional local branch name.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub branch: Option<String>,
    /// Optional workspace path or logical workspace label.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub workspace: Option<String>,
}

/// One compatibility claim in a baseline.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BaselineEntry {
    /// Stable entry identifier. Other documents reference this value.
    pub id: String,
    /// Short human-readable entry title.
    pub title: String,
    /// Product or compiler surface being compared.
    pub surface: CompatibilitySurface,
    /// Upstream source artifact, issue, test, or behavior anchor.
    pub upstream_artifact: String,
    /// Optional local source artifact, test, or behavior anchor.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub local_artifact: Option<String>,
    /// Expected upstream and local behavior relationship.
    pub expectation: CompatibilityExpectation,
    /// Current baseline status before run-specific result accounting.
    pub status: BaselineStatus,
    /// Optional labels for filtering and ownership.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub labels: Vec<String>,
}

/// Expected behavior relationship for a baseline entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompatibilityExpectation {
    /// Upstream Rust behavior being matched or intentionally not matched.
    pub upstream_behavior: String,
    /// Local Trust behavior expected for this baseline entry.
    pub local_behavior: String,
    /// Rule that explains how to classify the entry as compatible.
    pub compatibility_rule: String,
}

/// Compatibility surface categories.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CompatibilitySurface {
    /// Command-line behavior, flags, exit codes, or emitted files.
    Cli,
    /// Diagnostic text, spans, codes, or suggestions.
    CompilerDiagnostic,
    /// HIR lowering or analysis behavior.
    Hir,
    /// MIR construction, transforms, or semantics.
    Mir,
    /// Type checking, trait solving, borrow checking, or inference behavior.
    TypeSystem,
    /// Standard library API or semantics.
    StandardLibrary,
    /// Cargo-facing integration behavior.
    Cargo,
    /// Target specification, ABI, or platform behavior.
    Target,
    /// Trust verification pipeline behavior tied to upstream semantics.
    Verification,
    /// Explicit escape hatch for entries that do not fit a known surface.
    Other,
}

/// Baseline status before run-specific accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BaselineStatus {
    /// Local behavior is expected to match upstream.
    Compatible,
    /// Local behavior intentionally or accidentally diverges from upstream.
    Diverged,
    /// Upstream behavior exists but local support is not present yet.
    MissingLocal,
    /// Local behavior exists but upstream no longer has a matching anchor.
    MissingUpstream,
    /// The entry has not been classified yet.
    Unknown,
}

/// Ledger of known exceptions to baseline compatibility.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExceptionLedger {
    /// Version of this accounting schema.
    pub schema_version: String,
    /// Exception records keyed by stable exception id.
    pub exceptions: Vec<CompatibilityException>,
}

/// One allowed compatibility exception.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompatibilityException {
    /// Stable exception identifier.
    pub id: String,
    /// Baseline entry waived or explained by this exception.
    pub baseline_entry_id: String,
    /// Short human-readable title.
    pub title: String,
    /// Exception class used for reporting and prioritization.
    pub class: ExceptionClass,
    /// Current exception lifecycle status.
    pub status: ExceptionStatus,
    /// Human or team responsible for retiring or reviewing the exception.
    pub owner: String,
    /// Why this exception exists.
    pub reason: String,
    /// Optional expiry date in `YYYY-MM-DD` form.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expires_on: Option<String>,
    /// Optional upstream issue, PR, commit, or URL.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub upstream_reference: Option<String>,
    /// Optional local issue, PR, commit, or URL.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub local_reference: Option<String>,
}

/// Exception classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExceptionClass {
    /// Local behavior intentionally differs from upstream.
    IntentionalDivergence,
    /// Upstream behavior is known to be wrong or unstable.
    UpstreamBug,
    /// Local implementation is incomplete or wrong.
    LocalBug,
    /// Behavior differs only on a target or platform subset.
    PlatformGap,
    /// Behavior is experimental and not ready for compatibility gating.
    ExperimentalFeature,
    /// Accounting metadata exists but is incomplete.
    MissingMetadata,
}

/// Exception lifecycle status.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExceptionStatus {
    /// May currently waive a divergent result.
    Active,
    /// No longer valid because its review date has elapsed or policy expired it.
    Expired,
    /// Retired because upstream or local behavior changed.
    Resolved,
}

/// Ledger of upstream fixes that affect local compatibility accounting.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UpstreamFixLedger {
    /// Version of this accounting schema.
    pub schema_version: String,
    /// Optional upstream revision through which this ledger was reviewed for
    /// applicable fixes after the baseline snapshot.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tracked_until_revision: Option<String>,
    /// Upstream fix records keyed by stable fix id.
    pub fixes: Vec<UpstreamFix>,
}

/// One upstream fix relevant to a baseline entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UpstreamFix {
    /// Stable upstream fix identifier.
    pub id: String,
    /// Baseline entry affected by this upstream fix.
    pub baseline_entry_id: String,
    /// Short human-readable title.
    pub title: String,
    /// Upstream issue, PR, commit, or URL.
    pub upstream_reference: String,
    /// Current upstream fix lifecycle status.
    pub status: UpstreamFixStatus,
    /// Local action expected after observing this upstream fix.
    pub local_action: LocalFixAction,
    /// Optional upstream landing date in `YYYY-MM-DD` form.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub landed_on: Option<String>,
    /// Optional upstream revision containing the fix.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub landed_in_revision: Option<String>,
    /// Optional upstream release that contains the fix.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub released_in: Option<String>,
}

/// Upstream fix lifecycle status.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UpstreamFixStatus {
    /// Proposed upstream but not landed.
    Proposed,
    /// Landed upstream but not known to be in a release.
    Landed,
    /// Available in an upstream release.
    Released,
    /// Backported to a stable upstream release.
    Backported,
    /// The upstream fix was reverted.
    Reverted,
}

/// Local action expected after an upstream fix.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LocalFixAction {
    /// No local action is required.
    NoneNeeded,
    /// Rebase or regenerate the local baseline.
    RebaseBaseline,
    /// Cherry-pick the upstream change.
    CherryPick,
    /// Reimplement or port the upstream fix locally.
    PortFix,
    /// Remove or update a matching exception.
    DropException,
    /// Track the fix for reporting only.
    TrackOnly,
}

/// Run-specific compatibility result summary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompatibilityResultSummary {
    /// Version of this accounting schema.
    pub schema_version: String,
    /// Baseline identifier used for this run.
    pub baseline_id: String,
    /// Run date in `YYYY-MM-DD` form.
    pub generated_on: String,
    /// Optional run or CI job identifier.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub run_id: Option<String>,
    /// Optional local repository HEAD used to produce this summary.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repo_head: Option<String>,
    /// Optional dirty-worktree marker for the producing repository.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub repo_dirty: Option<bool>,
    /// Optional upstream Rust revision used for this run.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub upstream_revision: Option<String>,
    /// Optional target architecture for architecture-specific release evidence.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub target_arch: Option<String>,
    /// Optional target identifier or alias.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub target: Option<String>,
    /// Optional target triple.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub target_triple: Option<String>,
    /// Optional host architecture or triple.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub host: Option<String>,
    /// Optional host triple.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub host_triple: Option<String>,
    /// Optional architecture alias retained for downstream scorecards.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub architecture: Option<String>,
    /// Optional structured runner identity for provenance checks.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub runner: Option<CompatibilitySummaryRunner>,
    /// Declared totals for the result set.
    pub totals: ResultTotals,
    /// Per-baseline-entry run results.
    pub results: Vec<CompatibilityResult>,
}

impl CompatibilityResultSummary {
    /// Recount totals from the contained result rows.
    #[must_use]
    pub fn recount_totals(&self) -> ResultTotals {
        ResultTotals::from_results(&self.results)
    }
}

/// Structured runner identity attached to compatibility result summaries.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompatibilitySummaryRunner {
    /// Whether Python was used by the producing runner.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub python_used: Option<bool>,
    /// Runner implementation marker, usually `rust`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub implementation: Option<Value>,
    /// Runner language marker.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub language: Option<Value>,
    /// Runtime marker.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub runtime: Option<Value>,
    /// Runner kind marker.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kind: Option<Value>,
    /// Runner identity marker.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub identity: Option<Value>,
    /// Runner entrypoint marker.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub entrypoint: Option<Value>,
    /// Command line or command metadata for the runner.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub command: Option<Value>,
    /// Executable metadata for the runner.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub executable: Option<Value>,
    /// Path metadata for the runner.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path: Option<Value>,
    /// Runner name.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<Value>,
    /// Tool marker, usually `trust-upstream-compat`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool: Option<Value>,
    /// Package marker.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub package: Option<Value>,
    /// Binary marker.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub binary: Option<Value>,
    /// Additional runner metadata preserved for round-tripping.
    #[serde(default, flatten, skip_serializing_if = "BTreeMap::is_empty")]
    pub metadata: BTreeMap<String, Value>,
}

/// A single run-specific compatibility result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompatibilityResult {
    /// Baseline entry this result reports on.
    pub baseline_entry_id: String,
    /// Run-specific compatibility outcome.
    pub outcome: CompatibilityOutcome,
    /// Optional free-form observed result.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub observed: Option<String>,
    /// Optional exception used to waive this result.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exception_id: Option<String>,
    /// Optional upstream fix used to classify this result.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub upstream_fix_id: Option<String>,
}

/// Run-specific compatibility outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CompatibilityOutcome {
    /// Observed behavior matched the baseline expectation.
    Compatible,
    /// Observed behavior did not match and was not waived.
    Divergent,
    /// Observed divergence was waived by an active exception.
    Excepted,
    /// Observed behavior is explained by a tracked upstream fix.
    FixedUpstream,
    /// The run could not classify the entry.
    Unknown,
}

/// Summary counts for a run.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ResultTotals {
    /// Total result rows.
    pub total: u64,
    /// Compatible result rows.
    pub compatible: u64,
    /// Divergent result rows.
    pub divergent: u64,
    /// Rows waived by exceptions.
    pub excepted: u64,
    /// Rows explained by upstream fixes.
    pub fixed_upstream: u64,
    /// Rows that could not be classified.
    pub unknown: u64,
}

impl ResultTotals {
    /// Compute result totals from a slice of result rows.
    #[must_use]
    pub fn from_results(results: &[CompatibilityResult]) -> Self {
        let mut totals = Self { total: results.len() as u64, ..Self::default() };

        for result in results {
            match result.outcome {
                CompatibilityOutcome::Compatible => totals.compatible += 1,
                CompatibilityOutcome::Divergent => totals.divergent += 1,
                CompatibilityOutcome::Excepted => totals.excepted += 1,
                CompatibilityOutcome::FixedUpstream => totals.fixed_upstream += 1,
                CompatibilityOutcome::Unknown => totals.unknown += 1,
            }
        }

        totals
    }
}

/// Machine-readable inventory of tests that a full compatibility proof must
/// account for.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TestInventory {
    /// Version of this accounting schema.
    pub schema_version: String,
    /// Upstream Rust revision that supplied the pristine upstream test inputs.
    pub upstream_revision: String,
    /// Local Trust revision being tested.
    pub local_revision: String,
    /// Optional host triple for this inventory.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub host: Option<String>,
    /// Per-test inventory entries.
    pub tests: Vec<TestInventoryEntry>,
}

/// One test item in a compatibility proof inventory.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TestInventoryEntry {
    /// Stable test identifier used by results and exceptions.
    pub id: String,
    /// Logical suite name, for example `ui`, `run-make`, or `targo-trust`.
    pub suite: String,
    /// Repository-relative test path.
    pub path: String,
    /// Optional compiletest revision or equivalent subcase name.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub revision: Option<String>,
    /// Optional Git blob object id for the pristine upstream test input.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_git_blob: Option<String>,
    /// Source universe for this test.
    pub source: TestSource,
    /// Test runner family.
    pub kind: TestKind,
    /// Whether upstream considers this test applicable to the selected host.
    pub applicable: bool,
    /// Required when `applicable = false`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub inapplicable_reason: Option<String>,
    /// Optional content digest for the exact test input.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source_sha256: Option<String>,
}

/// The source universe a test belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TestSource {
    /// Test originated in the adopted pristine rust-lang/rust baseline.
    UpstreamRust,
    /// Test was added by Trust and is part of the Trust-specific corpus.
    TrustAdded,
}

/// Supported test runner families.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TestKind {
    /// Rust compiletest-managed test.
    Compiletest,
    /// Rustbuild/x.py unit, integration, or doc test.
    Rustbuild,
    /// Cargo test or Cargo's upstream test harness.
    Cargo,
    /// Rust tool test such as rustfmt, clippy, miri, or rust-analyzer.
    Tool,
    /// Python pytest test.
    Pytest,
    /// Shell-based end-to-end test.
    Shell,
    /// Other runner type.
    Other,
}

/// Per-test results from one compatibility proof run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TestResultReport {
    /// Version of this accounting schema.
    pub schema_version: String,
    /// Inventory identifier or digest used for this result report.
    pub inventory_id: String,
    /// Run date in `YYYY-MM-DD` form.
    pub generated_on: String,
    /// Exact command line used for the run.
    pub command: String,
    /// Per-test result rows.
    pub results: Vec<TestResult>,
}

/// One observed test result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TestResult {
    /// Test inventory id.
    pub test_id: String,
    /// Observed outcome.
    pub outcome: TestOutcome,
    /// Optional exception id used for a non-pass outcome.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exception_id: Option<String>,
    /// Optional concise observed details.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub observed: Option<String>,
    /// Optional path to a detailed log or diff artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub artifact: Option<String>,
}

/// Per-test outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TestOutcome {
    /// The test passed.
    Passed,
    /// The test failed.
    Failed,
    /// The test was skipped by Trust or the runner.
    Skipped,
    /// The test ran but produced an expected-output diff.
    Diffed,
    /// Upstream's own directives marked the test inapplicable to this host.
    UpstreamInapplicable,
    /// The runner could not classify the result.
    Unknown,
}

/// Per-test exception ledger for a compatibility proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TestExceptionLedger {
    /// Version of this accounting schema.
    pub schema_version: String,
    /// Per-test exception records.
    pub exceptions: Vec<TestException>,
}

/// One reviewed per-test exception.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TestException {
    /// Stable exception identifier.
    pub id: String,
    /// Test id this exception may waive.
    pub test_id: String,
    /// Suite copied from the inventory for review readability.
    pub suite: String,
    /// Path copied from the inventory for review readability.
    pub path: String,
    /// Optional revision copied from the inventory.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub revision: Option<String>,
    /// Exception class.
    pub kind: TestExceptionKind,
    /// Lifecycle status.
    pub status: ExceptionStatus,
    /// Human or team responsible for retiring the exception.
    pub owner: String,
    /// Closed reason code or concise prose.
    pub reason: String,
    /// Issue, PR, or tracker URL for the exception.
    pub issue: String,
    /// Local commit or change id that introduced the divergence, when known.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub introduced_by: Option<String>,
    /// Review date in `YYYY-MM-DD` form.
    pub reviewed_on: String,
    /// Expiry date in `YYYY-MM-DD` form.
    pub expires_on: String,
    /// Required bounded output patterns for diagnostic/output drift.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub allowed_patterns: Vec<String>,
}

/// Per-test exception classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TestExceptionKind {
    /// Trust currently fails a vanilla upstream test.
    ExpectedFail,
    /// Trust currently skips a vanilla upstream test for a Trust-specific reason.
    ExpectedSkip,
    /// Behavior is compatible but expected output text differs intentionally.
    ChangedDiagnostic,
    /// Trust intentionally diverges from upstream behavior.
    IntentionalDivergence,
    /// Local environment cannot run the test outside release evidence.
    EnvironmentalSkip,
}

/// Manifest of Trust-added commands that must be part of the proof.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustAddedTestManifest {
    /// Version of this accounting schema.
    pub schema_version: String,
    /// Command entries.
    pub commands: Vec<TrustAddedTestCommand>,
}

/// One Trust-added test command.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustAddedTestCommand {
    /// Stable command id.
    pub id: String,
    /// Exact command line.
    pub command: String,
    /// Inventory test ids covered by this command.
    pub covers: Vec<String>,
    /// Whether a release proof requires this command.
    pub required: bool,
}

/// Computed proof totals for per-test compatibility evidence.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TestProofTotals {
    /// Total inventory entries.
    pub total: u64,
    /// Upstream-origin test entries.
    pub upstream: u64,
    /// Trust-added test entries.
    pub trust_added: u64,
    /// Passing result rows.
    pub passed: u64,
    /// Upstream-inapplicable result rows.
    pub upstream_inapplicable: u64,
    /// Result rows waived by an active per-test exception.
    pub excepted: u64,
    /// Failed/skipped/diffed/unknown rows without valid accounting.
    pub unaccounted: u64,
}
