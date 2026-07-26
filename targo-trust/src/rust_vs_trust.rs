// Rust-vs-Trust comparison gate for hostile public review.
//
// This module deliberately treats superiority as a proof obligation, not a
// marketing claim. Unknowns, waivers, and regressions block the verdict by
// default and are emitted as AI-actionable directives.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::Duration;
use std::{env, fs};

use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::input_limits::{
    MAX_BINARY_ARTIFACT_BYTES, MAX_RELEASE_METADATA_BYTES, MAX_RELEASE_TRANSCRIPT_REPORT_BYTES,
    MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_file, read_bounded_utf8_file,
};
use crate::types::OutputFormat;

const SUITE_SCHEMA_VERSION: &str = "targo-trust.rust-vs-trust-suite.v1";
const REPORT_SCHEMA_VERSION: &str = "targo-trust.rust-vs-trust-report.v1";
const PROGRAM_INDEX_REPORT_SCHEMA: &str = "trust.compile-verify-program-index.report.v1";
const PROOF_DESIGN_VERIFIER_EVIDENCE_SCHEMA: &str =
    "trust.compile-verify-program-index.proof-design-verifier-evidence.v1";
const PROGRAM_INDEX_RUNTIME_PARITY_SCHEMA: &str = "trust.program-index.runtime-output-parity.v1";
const PROGRAM_INDEX_COMPILE_MEASUREMENT_PROFILE_SCHEMA: &str =
    "trust.program-index.compile-measurement-profile.v1";
const UNSUPPORTED_FRONTEND_LOWERING_GATE_SCHEMA: &str =
    "trust.program-index.unsupported-frontend-lowering-gate.v1";
const UNSUPPORTED_MIR_GATE_SCHEMA: &str = "trust.program-index.unsupported-mir-gate.v1";
const STRICT_SUPERIORITY_PERFORMANCE_SCHEMA: &str =
    "trust.strict-superiority.performance-evidence.v1";
const PROGRAM_INDEX_COMPILE_RESOURCE_USAGE_SOURCE: &str = "os.wait4";
const PROGRAM_INDEX_COMPILE_RESOURCE_SECONDS_TOLERANCE: f64 = 0.000_001;
const RELEASE_REPORT_SCHEMA: &str = "trust.release-report.v1";
const UPSTREAM_COMPAT_SUMMARY_SCHEMA_VERSION: &str = "0.1.0";
const PROOF_FUNCTIONAL_DIMENSION_ID: &str = "proof.functional-best-existing-tools";
const PROOF_FUNCTIONAL_EVIDENCE_COMMAND: &str =
    "targo trust benchmark program-index --suite proof-design --slots trust-verify --require-slots";
const PROOF_FUNCTIONAL_REPORT_FLAG: &str = "--proof-program-index-report";
const PROOF_UNSAFE_MEMORY_DIMENSION_ID: &str = "proof.unsafe-memory";
const PROOF_UNSAFE_MEMORY_REPORT_SCHEMA: &str = "trust.proof-unsafe-memory-report.v1";
const PROOF_UNSAFE_MEMORY_REPORT_FLAG: &str = "--proof-unsafe-memory-report";
const PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND: &str = "targo trust report --unsafe-memory";
const PROOF_CONCURRENCY_DIMENSION_ID: &str = "proof.concurrency";
const PROOF_CONCURRENCY_REPORT_SCHEMA: &str =
    "trust.proof-concurrency.authenticated-validation-report.v1";
const PROOF_CONCURRENCY_REPORT_FLAG: &str = "--proof-concurrency-report";
const PROOF_CONCURRENCY_EVIDENCE_COMMAND: &str =
    "not implemented: Trust-owned authenticated concurrency validation/replay producer";
const PROOF_CONCURRENCY_REQUIRED_OBLIGATION_KINDS: [&str; 3] =
    ["data_race_free", "atomic_ordering", "happens_before"];
const PROGRAM_INDEX_BENCHMARK_REPORT_FLAG: &str = "--program-index-benchmark-report";
const PRODUCT_PROOF_RELEASE_REPORT_FLAG: &str = "--product-proof-release-report";
const PROOF_FUNCTIONAL_SUITE: &str = "proof-design";
const PROOF_FUNCTIONAL_SLOT: &str = "trust-verify";
const PROGRAM_INDEX_RUNTIME_BASELINE_SLOT: &str = "upstream-rustc";
const PROGRAM_INDEX_RUNTIME_TRUST_SLOT: &str = "trust-noverify";
const PRODUCT_PROOF_BINARY_ROUNDTRIP_DIMENSION_ID: &str = "proof.binary-source-roundtrip";
const PRODUCT_PROOF_BINARY_DECOMP_COMPONENT: &str = "binary/decomp gates";
const PRODUCT_PROOF_EVIDENCE_SCHEMA: &str = "trust.product-proof.v1";
const UPSTREAM_COMPAT_MANIFEST: &str = "crates/trust-upstream-compat/Cargo.toml";
const IDENTITY_PROBE_MAX_STREAM_BYTES: usize = 64 * 1024;
const IDENTITY_PROBE_TIMEOUT: Duration = Duration::from_secs(10);
const UPSTREAM_METADATA_MAX_STREAM_BYTES: usize = 64 * 1024 * 1024;
const UPSTREAM_METADATA_TIMEOUT: Duration = Duration::from_secs(5 * 60);
const COMPILE_BACK_REQUIRED_EVIDENCE: [&str; 8] = [
    "compile-back-artifact-digests-bound",
    "compile-back-lifted-binary-trust_ir-sha256",
    "compile-back-rust-source-sha256",
    "compile-back-reconstructed-trust_ir-sha256",
    "compile-back-refinement-artifact-sha256",
    "compile-back-root-artifact-sha256",
    "compile-back-selected-image-sha256",
    "compile-back-selected-image-range",
];
const TEMPLATE: &str = r#"# Rust-vs-Trust toolchain comparison suite.
schema_version = "targo-trust.rust-vs-trust-suite.v1"
suite_id = "local-rust-vs-trust"

[policy]
require_no_unknowns = true
require_no_regressions = true
require_compatibility_floor = true
require_evidence_for_required = true
require_trust_advantage = true
max_performance_regression_pct = 0.0
min_performance_advantage_pct = 0.000001
min_feature_advantage_pct = 0.0

[[dimensions]]
id = "toolchain.rustc.compatibility"
title = "rustc-compatible compiler surface"
category = "compatibility"
metric = "pass_rate"
required = true
comparison_baseline = "rustc"
rust_value = 1.0
trust_value = 1.0
higher_is_better = true
evidence = ["targo trust domination upstream-tests --release"]
ai_hint = "Run the upstream Rust compatibility gate on the reviewed commit and eliminate every non-compatible row."

[[dimensions]]
id = "proof.overflow"
title = "Detect integer overflow bugs Rust accepts"
category = "verification"
metric = "score"
required = true
comparison_baseline = "rustc without external verifier plugins"
rust_value = 0.0
trust_value = 1.0
higher_is_better = true
evidence = ["targo trust check examples/verify_shift_overflow.rs --format json"]
ai_hint = "Keep a small reproducible proof transcript that shows Trust finds a real Rust-accepted bug."

[[dimensions]]
id = "proof.functional-best-existing-tools"
title = "Functional proof capability beyond Rust plus existing verifier tools"
category = "verification"
metric = "score"
required = true
comparison_baseline = "best practical Rust stack using Kani, Creusot, Prusti, Verus, MIRAI, Miri, sanitizers, Z3, and manual specs"
status = "unknown"
evidence = []
ai_hint = "Run targo trust benchmark program-index --suite proof-design --slots trust-verify --require-slots and pass the generated trust.compile-verify-program-index.report.v1 report with --proof-program-index-report."

[[dimensions]]
id = "proof.unsafe-memory"
title = "Unsafe-code memory proof coverage"
category = "safety"
metric = "pass_rate"
required = true
comparison_baseline = "Rust unsafe review plus Miri/sanitizers/Kani/Creusot-style bounded or annotated checks"
status = "unknown"
evidence = []
ai_hint = "Run targo trust report --unsafe-memory and pass a trust.proof-unsafe-memory-report.v1 wrapper with --proof-unsafe-memory-report."

[[dimensions]]
id = "proof.concurrency"
title = "Concurrency, atomics, and data-race proof coverage"
category = "safety"
metric = "pass_rate"
required = true
comparison_baseline = "Rust Send/Sync type checks plus Loom/Miri/sanitizers/manual model checking"
status = "unknown"
evidence = []
ai_hint = "The proof.concurrency lane is fail-closed until a Trust-owned authenticated validator/replayer emits trust.proof-concurrency.authenticated-validation-report.v1 for --proof-concurrency-report; artifact inventories and demo reports are non-proof."

[[dimensions]]
id = "performance.clean_build"
title = "Clean build wall time"
category = "performance"
metric = "latency_ms"
required = true
comparison_baseline = "rustc clean compile, same target, same optimization profile"
rust_value = 1000.0
trust_value = 1000.0
higher_is_better = false
evidence = ["replace with exact benchmark command, machine, commit, and raw log"]
ai_hint = "Replace placeholder timing with a reproducible Rust-vs-Trust benchmark transcript."
"#;

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct RustVsTrustArgs {
    format: OutputFormat,
    suite: Option<PathBuf>,
    compat_summary: Vec<PathBuf>,
    proof_program_index_report: Option<PathBuf>,
    proof_unsafe_memory_report: Option<PathBuf>,
    proof_concurrency_report: Option<PathBuf>,
    program_index_benchmark_report: Vec<PathBuf>,
    product_proof_release_report: Option<PathBuf>,
    out: Option<PathBuf>,
    write_template: Option<PathBuf>,
    allow_missing_evidence: bool,
    allow_exceptions: bool,
    min_performance_advantage_pct: Option<f64>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct SuiteInput {
    schema_version: String,
    #[serde(default)]
    suite_id: Option<String>,
    #[serde(default)]
    policy: PolicyInput,
    #[serde(default)]
    dimensions: Vec<DimensionInput>,
}

#[derive(Debug, Clone, Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct PolicyInput {
    #[serde(default)]
    require_no_unknowns: Option<bool>,
    #[serde(default)]
    require_no_regressions: Option<bool>,
    #[serde(default)]
    require_compatibility_floor: Option<bool>,
    #[serde(default)]
    require_evidence_for_required: Option<bool>,
    #[serde(default)]
    require_trust_advantage: Option<bool>,
    #[serde(default)]
    max_performance_regression_pct: Option<f64>,
    #[serde(default)]
    min_performance_advantage_pct: Option<f64>,
    #[serde(default)]
    min_feature_advantage_pct: Option<f64>,
}

#[derive(Debug, Clone, Serialize)]
struct EffectivePolicy {
    require_no_unknowns: bool,
    require_no_regressions: bool,
    require_compatibility_floor: bool,
    require_evidence_for_required: bool,
    require_trust_advantage: bool,
    allow_exceptions: bool,
    max_performance_regression_pct: f64,
    min_performance_advantage_pct: f64,
    min_feature_advantage_pct: f64,
}

impl EffectivePolicy {
    fn from_input(input: &PolicyInput) -> Self {
        Self {
            require_no_unknowns: input.require_no_unknowns.unwrap_or(true),
            require_no_regressions: input.require_no_regressions.unwrap_or(true),
            require_compatibility_floor: input.require_compatibility_floor.unwrap_or(true),
            require_evidence_for_required: input.require_evidence_for_required.unwrap_or(true),
            require_trust_advantage: input.require_trust_advantage.unwrap_or(true),
            allow_exceptions: false,
            max_performance_regression_pct: input.max_performance_regression_pct.unwrap_or(0.0),
            min_performance_advantage_pct: input.min_performance_advantage_pct.unwrap_or(0.0),
            min_feature_advantage_pct: input.min_feature_advantage_pct.unwrap_or(0.0),
        }
    }
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct DimensionInput {
    id: String,
    title: String,
    category: DimensionCategory,
    #[serde(default)]
    metric: Option<MetricKind>,
    #[serde(default)]
    comparison_baseline: Option<String>,
    #[serde(default = "default_true")]
    required: bool,
    #[serde(default)]
    rust_value: Option<f64>,
    #[serde(default)]
    trust_value: Option<f64>,
    #[serde(default)]
    higher_is_better: Option<bool>,
    #[serde(default)]
    min_trust_delta_pct: Option<f64>,
    #[serde(default)]
    max_trust_regression_pct: Option<f64>,
    #[serde(default)]
    status: Option<DeclaredStatus>,
    #[serde(default)]
    unit: Option<String>,
    #[serde(default = "default_weight")]
    weight: f64,
    #[serde(default)]
    evidence: Vec<String>,
    #[serde(default)]
    ai_hint: Option<String>,
    #[serde(default)]
    owner: Option<String>,
    #[serde(skip)]
    evidence_source: DimensionEvidenceSource,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum DimensionEvidenceSource {
    #[default]
    Manual,
    CompatibilitySummaryAggregate,
    ProgramIndexProofReport,
    ProofUnsafeMemoryReport,
    ProofConcurrencyReport,
    ProgramIndexRuntimeBinaryReport,
    ProductProofReleaseReport,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum DimensionCategory {
    Compatibility,
    Feature,
    Performance,
    Verification,
    Safety,
    Ergonomics,
    Distribution,
    AiGuidance,
    Other,
}

impl DimensionCategory {
    fn label(self) -> &'static str {
        match self {
            Self::Compatibility => "compatibility",
            Self::Feature => "feature",
            Self::Performance => "performance",
            Self::Verification => "verification",
            Self::Safety => "safety",
            Self::Ergonomics => "ergonomics",
            Self::Distribution => "distribution",
            Self::AiGuidance => "ai_guidance",
            Self::Other => "other",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum MetricKind {
    Score,
    PassRate,
    LatencyMs,
    Throughput,
    Count,
    BinarySizeBytes,
    MemoryBytes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum DeclaredStatus {
    Pass,
    Fail,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum Verdict {
    Superior,
    NotSuperior,
    Unproven,
}

impl Verdict {
    fn label(self) -> &'static str {
        match self {
            Self::Superior => "SUPERIOR",
            Self::NotSuperior => "NOT SUPERIOR",
            Self::Unproven => "UNPROVEN",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum DimensionStatus {
    Pass,
    Fail,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
enum Severity {
    P0,
    P1,
    P2,
}

impl Severity {
    fn label(self) -> &'static str {
        match self {
            Self::P0 => "P0",
            Self::P1 => "P1",
            Self::P2 => "P2",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
enum BlockerKind {
    NoEvidence,
    MissingEvidence,
    InconsistentEvidence,
    UnknownResult,
    DeclaredFailure,
    Regression,
    CompatibilityNotProven,
    NoTrustAdvantage,
    InvalidMetric,
}

#[derive(Debug, Clone, Serialize)]
struct Blocker {
    severity: Severity,
    kind: BlockerKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    dimension_id: Option<String>,
    message: String,
    action: String,
}

#[derive(Debug, Clone, Serialize)]
struct AiDirective {
    priority: Severity,
    area: String,
    reason: String,
    action: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    owner: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct DimensionReport {
    id: String,
    title: String,
    category: DimensionCategory,
    required: bool,
    status: DimensionStatus,
    #[serde(skip_serializing_if = "Option::is_none")]
    metric: Option<MetricKind>,
    #[serde(skip_serializing_if = "Option::is_none")]
    comparison_baseline: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    unit: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    rust_value: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    trust_value: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    delta_pct: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    min_trust_delta_pct: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    max_trust_regression_pct: Option<f64>,
    trust_is_better: bool,
    trust_is_worse: bool,
    weight: f64,
    evidence: Vec<String>,
    blockers: Vec<Blocker>,
    #[serde(skip_serializing_if = "Option::is_none")]
    owner: Option<String>,
    recommendation: String,
}

#[derive(Debug, Clone, Serialize)]
struct RustVsTrustSummary {
    total_dimensions: usize,
    required_dimensions: usize,
    passed: usize,
    failed: usize,
    unknown: usize,
    missing_evidence: usize,
    regressions: usize,
    compatibility_blockers: usize,
    trust_advantage_dimensions: usize,
    rust_relative_index: f64,
    trust_relative_index: f64,
}

#[derive(Debug, Clone, Serialize)]
struct CompatSummaryIngestReport {
    path: String,
    rows: usize,
    compatible: usize,
    non_compatible: usize,
    unknown: usize,
    exceptions_rejected: bool,
}

#[derive(Debug, Clone)]
struct EvidenceCommitBinding {
    source: &'static str,
    path: String,
    commit: String,
}

impl EvidenceCommitBinding {
    fn new(source: &'static str, path: &Path, commit: String) -> Self {
        Self { source, path: path.display().to_string(), commit }
    }
}

#[derive(Debug, Clone, Serialize)]
struct EvidenceRequirements {
    proof_functional_best_existing_tools: EvidenceRequirement,
    proof_unsafe_memory: UnsafeMemoryEvidenceRequirement,
    proof_concurrency: ProofConcurrencyEvidenceRequirement,
    proof_binary_source_roundtrip: BinarySourceRoundtripEvidenceRequirement,
}

#[derive(Debug, Clone, Serialize)]
struct EvidenceRequirement {
    dimension_id: &'static str,
    required_flag: &'static str,
    required_command: &'static str,
    expected_schema: &'static str,
    required_suite: &'static str,
    required_slot: &'static str,
    current_json_required: bool,
    fail_closed_conditions: Vec<&'static str>,
}

#[derive(Debug, Clone, Serialize)]
struct BinarySourceRoundtripEvidenceRequirement {
    dimension_id: &'static str,
    required_flag: &'static str,
    required_command: &'static str,
    expected_schema: &'static str,
    required_profile: &'static str,
    required_gate: &'static str,
    required_product_proof_component: &'static str,
    required_product_proof_component_status: &'static str,
    required_compile_back_evidence_kinds: Vec<&'static str>,
    required_compile_back_evidence_declaration: bool,
    materialized_artifacts_required: bool,
    materialized_artifact_reference_format: &'static str,
    current_json_required: bool,
    fail_closed_conditions: Vec<&'static str>,
}

#[derive(Debug, Clone, Serialize)]
struct UnsafeMemoryEvidenceRequirement {
    dimension_id: &'static str,
    required_flag: &'static str,
    required_command: &'static str,
    expected_schema: &'static str,
    required_producer_command: &'static str,
    required_producer_native: bool,
    proof_report_hash_required: bool,
    unsupported_must_be_empty: bool,
    coverage_counts_required: Vec<&'static str>,
    current_json_required: bool,
    fail_closed_conditions: Vec<&'static str>,
}

#[derive(Debug, Clone, Serialize)]
struct ProofConcurrencyEvidenceRequirement {
    dimension_id: &'static str,
    required_flag: &'static str,
    required_command: &'static str,
    expected_schema: &'static str,
    required_obligation_kinds: Vec<&'static str>,
    current_json_required: bool,
    fail_closed_conditions: Vec<&'static str>,
}

#[derive(Debug, Clone, Serialize)]
struct RustVsTrustReport {
    schema_version: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    suite_id: Option<String>,
    verdict: Verdict,
    policy: EffectivePolicy,
    evidence_requirements: EvidenceRequirements,
    summary: RustVsTrustSummary,
    #[serde(skip_serializing_if = "Option::is_none")]
    compatibility_summary: Option<CompatSummaryIngestReport>,
    blockers: Vec<Blocker>,
    ai_directives: Vec<AiDirective>,
    dimensions: Vec<DimensionReport>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CompatibilityResultSummaryInput {
    schema_version: String,
    #[allow(dead_code)]
    baseline_id: String,
    #[allow(dead_code)]
    #[serde(default)]
    generated_on: Option<String>,
    #[allow(dead_code)]
    #[serde(default)]
    run_id: Option<String>,
    #[serde(default)]
    repo_head: Option<String>,
    #[serde(default)]
    repo_dirty: Option<bool>,
    #[serde(default)]
    upstream_revision: Option<String>,
    #[serde(default)]
    runner: Option<Value>,
    #[serde(default)]
    totals: Option<CompatibilityResultTotalsInput>,
    results: Vec<CompatibilityResultInput>,
    #[serde(default)]
    target_arch: Option<String>,
    #[allow(dead_code)]
    #[serde(default)]
    target: Option<String>,
    #[allow(dead_code)]
    #[serde(default)]
    target_triple: Option<String>,
    #[allow(dead_code)]
    #[serde(default)]
    host: Option<String>,
    #[allow(dead_code)]
    #[serde(default)]
    host_triple: Option<String>,
    #[allow(dead_code)]
    #[serde(default)]
    architecture: Option<String>,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
struct CompatibilityResultTotalsInput {
    total: u64,
    compatible: u64,
    divergent: u64,
    excepted: u64,
    fixed_upstream: u64,
    unknown: u64,
}

impl CompatibilityResultTotalsInput {
    fn from_results(results: &[CompatibilityResultInput]) -> Self {
        let mut totals = Self { total: results.len() as u64, ..Self::default() };
        for result in results {
            match result.outcome {
                CompatibilityOutcomeInput::Compatible => totals.compatible += 1,
                CompatibilityOutcomeInput::Divergent => totals.divergent += 1,
                CompatibilityOutcomeInput::Excepted => totals.excepted += 1,
                CompatibilityOutcomeInput::FixedUpstream => totals.fixed_upstream += 1,
                CompatibilityOutcomeInput::Unknown => totals.unknown += 1,
            }
        }
        totals
    }
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CompatibilityResultInput {
    baseline_entry_id: String,
    outcome: CompatibilityOutcomeInput,
    #[serde(default)]
    observed: Option<String>,
    #[serde(default)]
    exception_id: Option<String>,
    #[serde(default)]
    upstream_fix_id: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
enum CompatibilityOutcomeInput {
    Compatible,
    Divergent,
    Excepted,
    FixedUpstream,
    Unknown,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofUnsafeMemoryReportInput {
    schema: String,
    candidate_commit: String,
    repo_dirty: bool,
    producer: ProofUnsafeMemoryProducerInput,
    proof_report_path: String,
    proof_report_hash: String,
    coverage: ProofUnsafeMemoryCoverageInput,
    unsupported: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofUnsafeMemoryProducerInput {
    command: String,
    native: bool,
}

#[derive(Debug, Clone, Copy, Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofUnsafeMemoryCoverageInput {
    unsafe_blocks_total: u64,
    unsafe_blocks_proved: u64,
    unsafe_operations_total: u64,
    unsafe_operations_proved: u64,
    memory_obligations_total: u64,
    memory_obligations_proved: u64,
}

pub(crate) fn run_subcommand(args: &[String]) -> ExitCode {
    if args.first().is_some_and(|arg| arg == "upstream-rust-tests") {
        eprintln!(
            "targo trust domination: `upstream-rust-tests` has been removed; use `targo trust domination upstream-tests`"
        );
        return ExitCode::from(2);
    }
    if args.first().is_some_and(|arg| is_upstream_tests_subcommand(arg)) {
        return run_upstream_tests_subcommand(&args[1..]);
    }
    if args.first().is_some_and(|arg| is_trust_added_subcommand(arg)) {
        return run_trust_added_subcommand(&args[1..]);
    }

    let help_requested = args.iter().any(|arg| arg == "--help" || arg == "-h");
    if args.len() == 1 && help_requested {
        print!("{}", usage_text());
        return ExitCode::SUCCESS;
    }
    if help_requested {
        eprintln!("targo trust domination: `--help` must be used by itself");
        return ExitCode::from(2);
    }

    let args = match parse_args(args) {
        Ok(args) => args,
        Err(error) => {
            eprintln!("targo trust: {error}");
            return ExitCode::from(2);
        }
    };

    if matches!(args.format, OutputFormat::Html) {
        eprintln!(
            "targo trust domination: --format html is not supported yet; use terminal or json"
        );
        return ExitCode::from(2);
    }

    if let Some(path) = args.write_template.as_deref() {
        if let Err(error) = write_template(path) {
            eprintln!("targo trust: {error:#}");
            return ExitCode::from(2);
        }
        return ExitCode::SUCCESS;
    }

    let report = match build_report(&args) {
        Ok(report) => report,
        Err(error) => {
            eprintln!("targo trust: {error:#}");
            return ExitCode::from(2);
        }
    };

    let rendered = match args.format {
        OutputFormat::Json => match serde_json::to_string_pretty(&report) {
            Ok(json) => json + "\n",
            Err(error) => {
                eprintln!("targo trust domination: failed to serialize report: {error}");
                return ExitCode::from(2);
            }
        },
        OutputFormat::Terminal => render_terminal(&report),
        OutputFormat::Html => unreachable!("HTML rejected before report rendering"),
    };

    if let Some(path) = args.out.as_deref() {
        if let Err(error) = fs::write(path, &rendered) {
            eprintln!("targo trust: failed to write {}: {error}", path.display());
            return ExitCode::from(2);
        }
    } else {
        print!("{rendered}");
    }

    match report.verdict {
        Verdict::Superior => ExitCode::SUCCESS,
        Verdict::NotSuperior | Verdict::Unproven => ExitCode::FAILURE,
    }
}

pub(crate) fn usage_text() -> String {
    [
        "targo trust domination: fail-closed Rust-vs-Trust superiority gate",
        "",
        "Usage:",
        "  targo trust domination [--json]",
        "  targo trust domination --suite <path> [--compat-summary <path> ...] [--json]",
        "  targo trust domination --compat-summary <path> [--compat-summary <path> ...] [--json]",
        "  targo trust domination --write-template <path>",
        "  targo trust domination upstream-tests [port options]",
        "  targo trust domination trust-added [--strict] [--release] <mode>",
        "",
        "Options:",
        "  --suite <path>                 TOML/JSON comparison suite with feature, proof, and performance dimensions",
        "  --compat-summary <path>        trust-upstream-compat summary JSON/TOML; repeat for each architecture",
        "  --proof-program-index-report <path>  Program-index report JSON for proof.functional-best-existing-tools",
        "  --proof-unsafe-memory-report <path>  Structured unsafe-memory proof report JSON for proof.unsafe-memory",
        "  --proof-concurrency-report <path>  Structured proof-concurrency report JSON for proof.concurrency",
        "  --program-index-benchmark-report <path>  Program-index report JSON; repeat for cold, warm, and per-arch evidence",
        "  --product-proof-release-report <path>  Product-proof release report JSON for binary/source roundtrip evidence",
        "  --out <path>                   Write the rendered report instead of stdout",
        "  --write-template <path>        Write a starter suite template; use '-' for stdout",
        "  --format <terminal|json>       Output format (terminal default)",
        "  --json                         Alias for --format json",
        "  --allow-missing-evidence       Draft mode: missing required evidence is a directive, not a verdict blocker",
        "  --allow-exceptions             Draft mode: compatibility exceptions are not treated as hard blockers",
        "  --min-performance-advantage-pct <N>  Require Trust to beat Rust by at least N percent on every performance metric",
        "",
        "Verdict contract:",
        "  Exit 0 only when Trust is evidence-backed, Rust-compatible, regression-free, and has at least one measured advantage.",
        "  Exit 1 when the comparison is valid but Trust is not yet superior or not yet proven.",
        "  Exit 2 for usage, parsing, or report I/O errors.",
        "",
        "Upstream test porting:",
        "  `targo trust domination upstream-tests` is the canonical Rust-owned front door for re-importing latest upstream Rust tests, adapting trivial Trust drift with an audit log, and writing the scorecard.",
        "  It dispatches the Rust `trust-upstream-compat port` engine; Python is not used.",
        "",
        "Trust-added inventory:",
        "  `targo trust domination trust-added <mode>` is the manifest-facing Rust CLI for Trust-specific proof commands.",
    ]
    .join("\n")
        + "\n"
}

fn is_upstream_tests_subcommand(arg: &str) -> bool {
    arg == "upstream-tests"
}

fn is_trust_added_subcommand(arg: &str) -> bool {
    matches!(arg, "trust-added" | "added-tests")
}

fn upstream_tests_requires_trust_cargo(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "--release")
}

fn run_upstream_tests_subcommand(args: &[String]) -> ExitCode {
    let help_requested = args.iter().any(|arg| arg == "--help" || arg == "-h");
    if args.len() == 1 && help_requested {
        print!("{}", upstream_tests_usage_text());
        return ExitCode::SUCCESS;
    }
    if help_requested {
        eprintln!("targo trust domination upstream-tests: `--help` must be used by itself");
        return ExitCode::from(2);
    }

    let root = repo_root_for_upstream_tests();
    let cargo_driver =
        match resolve_upstream_compat_cargo(&root, upstream_tests_requires_trust_cargo(args)) {
            Ok(driver) => driver,
            Err(error) => {
                eprintln!("targo trust: {error}");
                return ExitCode::from(2);
            }
        };
    eprintln!(
        "targo trust domination upstream-tests: validating trust-upstream-compat manifest/lockfile with --locked"
    );
    if let Err(error) = preflight_upstream_compat_lockfile(&cargo_driver, &root) {
        eprintln!("targo trust: {error:#}");
        return ExitCode::from(2);
    }
    let upstream_compat_cargo_env = upstream_compat_child_cargo_env(&cargo_driver);
    let command = build_upstream_tests_command(cargo_driver, &root, args);

    eprintln!("targo trust domination upstream-tests: dispatching Rust upstream porting CLI");
    let Some(program) = command.first() else {
        eprintln!("targo trust: internal error: empty upstream-tests command");
        return ExitCode::from(2);
    };
    let mut child = Command::new(program);
    child.args(&command[1..]).current_dir(&root);
    if let Some(value) = upstream_compat_cargo_env.as_deref() {
        child.env("TRUST_UPSTREAM_COMPAT_CARGO", value);
        child.env("TRUST_TARGO_BIN", value);
    }
    // This is the interactive, potentially long-running porting engine. It
    // deliberately inherits the user's terminal and lifetime; metadata and
    // identity probes around it use bounded capture instead.
    let status = child.status();
    match status {
        Ok(status) => ExitCode::from(status.code().unwrap_or(1) as u8),
        Err(error) => {
            eprintln!("targo trust: failed to run upstream-tests engine: {error}");
            ExitCode::from(2)
        }
    }
}

fn build_upstream_tests_command(
    mut cargo_driver: Vec<String>,
    root: &Path,
    args: &[String],
) -> Vec<String> {
    cargo_driver.extend([
        "run".to_string(),
        "--manifest-path".to_string(),
        upstream_compat_manifest_path(root).to_string_lossy().into_owned(),
        "--locked".to_string(),
        "--".to_string(),
        "port".to_string(),
    ]);
    cargo_driver.extend(args.iter().cloned());
    cargo_driver
}

fn upstream_compat_child_cargo_env(cargo_driver: &[String]) -> Option<String> {
    (!cargo_driver.is_empty()).then(|| cargo_driver.join(" "))
}

fn preflight_upstream_compat_lockfile(cargo_driver: &[String], root: &Path) -> Result<()> {
    let command = build_upstream_compat_lockfile_preflight_command(cargo_driver.to_vec(), root);
    let Some(program) = command.first() else {
        bail!("internal error: empty trust-upstream-compat lockfile preflight command");
    };

    let mut process = Command::new(program);
    process.args(&command[1..]).current_dir(root);
    let output = crate::bounded_process::output(
        &mut process,
        "trust-upstream-compat lockfile preflight",
        UPSTREAM_METADATA_MAX_STREAM_BYTES,
        UPSTREAM_METADATA_TIMEOUT,
    )
    .map_err(anyhow::Error::msg)
    .with_context(|| {
        format!(
            "failed to run trust-upstream-compat lockfile preflight: {}",
            display_command(&command)
        )
    })?;
    if output.status.success() {
        return Ok(());
    }

    bail!(
        "trust-upstream-compat manifest/lockfile preflight failed under --locked before porting\ncommand: {}\nstatus: {}\nstdout:\n{}\nstderr:\n{}\nRefresh {} with `targo update --manifest-path {}` before retrying.",
        display_command(&command),
        output.status,
        command_output_text(&output.stdout),
        command_output_text(&output.stderr),
        UPSTREAM_COMPAT_MANIFEST,
        UPSTREAM_COMPAT_MANIFEST
    )
}

fn build_upstream_compat_lockfile_preflight_command(
    mut cargo_driver: Vec<String>,
    root: &Path,
) -> Vec<String> {
    cargo_driver.extend([
        "metadata".to_string(),
        "--manifest-path".to_string(),
        upstream_compat_manifest_path(root).to_string_lossy().into_owned(),
        "--locked".to_string(),
        "--format-version".to_string(),
        "1".to_string(),
        "--no-deps".to_string(),
    ]);
    cargo_driver
}

fn upstream_compat_manifest_path(root: &Path) -> PathBuf {
    root.join(UPSTREAM_COMPAT_MANIFEST)
}

fn display_command(command: &[String]) -> String {
    command.join(" ")
}

fn command_output_text(bytes: &[u8]) -> String {
    let text = String::from_utf8_lossy(bytes);
    let trimmed = text.trim();
    if trimmed.is_empty() { "<empty>".to_string() } else { trimmed.to_string() }
}

fn upstream_tests_usage_text() -> String {
    [
        "targo trust domination upstream-tests: repeatable upstream Rust test porting",
        "",
        "Usage:",
        "  targo trust domination upstream-tests [--no-execute] [--no-apply] [--release]",
        "  targo trust domination upstream-tests --release --proof-mode full --execute --no-apply --summary-out reports/strict-superiority/<run-id>/upstream-rust/<arch>/compat-summary.json --out-dir reports/strict-superiority/<run-id>/upstream-rust/<arch>/porting",
        "",
        "Common options:",
        "  --baseline <path>             Upstream compatibility baseline (default tests/upstream-rust/baseline.toml)",
        "  --upstream-fixes <path>       Upstream fix ledger (default tests/upstream-rust/upstream-fixes.toml)",
        "  --test-exceptions <path>      Per-test exception ledger (default tests/upstream-rust/test-exceptions.toml)",
        "  --summary-out <path>          Write the domination-compatible compat summary at this path",
        "  --run-id <id>                 Stable run identifier recorded in the compat summary",
        "  --target-arch <arch>          Target architecture recorded in the compat summary",
        "  --target <target>             Target label recorded in the compat summary",
        "  --target-triple <triple>      Target triple recorded in the compat summary",
        "  --host <host>                 Host label recorded in the compat summary",
        "  --host-triple <triple>        Host triple recorded in the compat summary",
        "  --upstream-revision <rev>     Upstream Rust revision, including rust-lang/rust:HEAD",
        "  --upstream-remote <url>       Upstream Rust git remote",
        "  --out-dir <path>              Porting artifact directory",
        "  --execute                     Run the proof suite after import/adaptation (default)",
        "  --no-execute                  Re-import/adapt only or parse --scorecard-log",
        "  --apply                       Apply ported upstream overlay to tests/ (default)",
        "  --no-apply                    Leave tests/ untouched and write artifacts only",
        "  --no-fetch                    Resolve only exact/local refs; rejects symbolic remote refs",
        "  --scorecard-log <path>        Parse an existing log instead of executing",
        "  --bootstrap-args <args>       Extra direct Rust bootstrap args for execution",
        "  --max-files <n>               Bounded import for smoke/debug runs",
        "  --release                     Require Trust-owned targo for release evidence",
        "  --proof-mode auto|smoke|full  Full proof is required for unbounded auto runs",
        "",
        "Dispatch:",
        "  Dispatches the Rust `trust-upstream-compat port` command; Python is not used.",
    ]
    .join("\n")
        + "\n"
}

fn run_trust_added_subcommand(args: &[String]) -> ExitCode {
    let help_requested = args.iter().any(|arg| arg == "--help" || arg == "-h");
    let release_from_environment = env::var("TRUST_RELEASE_GATE").is_ok_and(|value| value == "1");
    let release_requested = args.iter().any(|arg| arg == "--release");

    if args.len() == 1 && help_requested && !release_from_environment {
        print!("{}", trust_added_usage_text());
        return ExitCode::SUCCESS;
    }
    if help_requested {
        if release_requested || release_from_environment {
            eprintln!(
                "targo trust domination trust-added: `--help` cannot be combined with a release request"
            );
        } else {
            eprintln!("targo trust domination trust-added: `--help` must be used by itself");
        }
        return ExitCode::from(2);
    }

    let mut strict = false;
    let mut release = false;
    let mut mode = None;
    for arg in args {
        match arg.as_str() {
            "--strict" => strict = true,
            "--release" => {
                strict = true;
                release = true;
            }
            other if other.starts_with('-') => {
                eprintln!("targo trust domination trust-added: unexpected option `{other}`");
                return ExitCode::from(2);
            }
            other => {
                if mode.replace(other.to_string()).is_some() {
                    eprintln!("targo trust domination trust-added: mode specified more than once");
                    return ExitCode::from(2);
                }
            }
        }
    }

    let Some(mode) = mode else {
        eprintln!("targo trust domination trust-added: missing mode");
        print!("{}", trust_added_usage_text());
        return ExitCode::from(2);
    };
    let Some(mode) = trust_added_mode(&mode) else {
        eprintln!("targo trust domination trust-added: unknown mode `{mode}`");
        print!("{}", trust_added_usage_text());
        return ExitCode::from(2);
    };

    // The legacy engine-facing environment spellings must hit the same
    // fail-closed boundary as the explicit flags. Otherwise an environment
    // variable could silently upgrade a command labelled as a local result.
    release = release || release_from_environment;
    strict = strict || release || env::var("TRUST_STRICT").is_ok_and(|value| value == "1");

    let release_note = if release {
        "release "
    } else if strict {
        "strict "
    } else {
        ""
    };

    // Rust-native ports remain useful local diagnostics, but none currently
    // has an independently authenticated, isolated child-process authority
    // boundary. A release request must therefore fail before executing any
    // ignored Stage2/bootstrap binary or consulting ambient Cargo state.
    if crate::trust_added::is_native_mode(mode) {
        if release {
            eprintln!(
                "targo trust domination trust-added: release mode `{mode}` is blocked: the native gate does not yet execute inside an independently authenticated, isolated environment with immutable tool provenance"
            );
            eprintln!(
                "  Run without `--release` only for a local diagnostic; that result can never satisfy `{mode}` release evidence."
            );
            return ExitCode::from(2);
        }
        eprintln!(
            "targo trust domination trust-added: {release_note}mode `{mode}` dispatching Rust-native local diagnostic gate"
        );
        return match crate::trust_added::run(&repo_root_from_manifest(), mode, strict, release) {
            Ok(()) => {
                println!();
                println!(
                    "=== targo trust domination trust-added ({mode}): LOCAL DIAGNOSTIC PASS ==="
                );
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("targo trust domination trust-added {mode}: FAIL: {error:#}");
                ExitCode::FAILURE
            }
        };
    }

    if let Some((diagnostic, missing_evidence)) = blocked_canonical_diagnostic(mode) {
        eprintln!(
            "targo trust domination trust-added: {release_note}canonical mode `{mode}` is blocked: {missing_evidence}"
        );
        eprintln!(
            "  The weaker `{diagnostic}` mode is runnable for local diagnostics, but can never satisfy `{mode}` release evidence."
        );
        eprintln!("  Manifest: tests/trust-added/manifest.toml");
        return ExitCode::from(2);
    }

    eprintln!(
        "targo trust domination trust-added: {release_note}mode `{mode}` is registered, but shell-backed execution is disabled"
    );
    eprintln!(
        "  Port this gate into Rust-native `targo trust` code or a native test before using it as Trust evidence."
    );
    eprintln!("  Manifest: tests/trust-added/manifest.toml");
    ExitCode::from(2)
}

fn blocked_canonical_diagnostic(mode: &str) -> Option<(&'static str, &'static str)> {
    Some(match mode {
        "installed" | "installed-default" => (
            "local-stage2-surface-smoke",
            "clean external-install/default evidence lacks an independently authenticated native verifier; ignored receipts are not authority",
        ),
        "trust-extra" => (
            "trust-extra-smoke",
            "strict typed corpus, semantic trust-cg parity, and non-synthetic native-suite proof evidence is absent",
        ),
        "public-distribution" => (
            "public-distribution-cull-smoke",
            "authenticated distribution roots, artifacts, checksums/signatures, and install evidence are absent",
        ),
        "prepublish" => (
            "prepublish-local-surface-smoke",
            "dist/checksum/clean-install evidence lacks a fresh authenticated receipt transaction and remains non-authoritative",
        ),
        "stage0-lineage" => (
            "stage0-metadata-coherence-smoke",
            "the ignored Stage2 receipt cannot authenticate the interpreter selected from its own contents",
        ),
        _ => return None,
    })
}

fn trust_added_mode(mode: &str) -> Option<&'static str> {
    match mode {
        "quick" => Some("quick"),
        "trustc-native" => Some("trustc-native"),
        "trust-added-compiletest" => Some("trust-added-compiletest"),
        "trust-extra" => Some("trust-extra"),
        "binary-decompilation-golden" => Some("binary-decompilation-golden"),
        "native-contracts-pipeline-v2" => Some("native-contracts-pipeline-v2"),
        "smoke" => Some("smoke"),
        "parity" => Some("parity"),
        "full" => Some("full"),
        "launch" => Some("launch"),
        "public-distribution" => Some("public-distribution"),
        "prepublish" => Some("prepublish"),
        "installed" => Some("installed"),
        "installed-default" => Some("installed-default"),
        "stage0-lineage" => Some("stage0-lineage"),
        "local-stage2-surface-smoke" => Some("local-stage2-surface-smoke"),
        "trust-extra-smoke" => Some("trust-extra-smoke"),
        "public-distribution-cull-smoke" => Some("public-distribution-cull-smoke"),
        "prepublish-local-surface-smoke" => Some("prepublish-local-surface-smoke"),
        "stage0-metadata-coherence-smoke" => Some("stage0-metadata-coherence-smoke"),
        _ => None,
    }
}

fn trust_added_usage_text() -> String {
    [
        "targo trust domination trust-added: Trust-added proof inventory",
        "",
        "Usage:",
        "  targo trust domination trust-added [--strict] [--release] <mode>",
        "",
        "Modes:",
        "  quick",
        "  trustc-native",
        "  trust-added-compiletest",
        "  trust-extra",
        "  binary-decompilation-golden",
        "  native-contracts-pipeline-v2",
        "  smoke",
        "  parity",
        "  full",
        "  launch",
        "  public-distribution",
        "  prepublish",
        "  installed",
        "  installed-default",
        "  stage0-lineage",
        "",
        "Diagnostic smoke modes (never canonical release evidence):",
        "  local-stage2-surface-smoke",
        "  trust-extra-smoke",
        "  public-distribution-cull-smoke",
        "  prepublish-local-surface-smoke",
        "  stage0-metadata-coherence-smoke",
        "",
        "Status:",
        "  Rust-native local diagnostics: quick, trust-added-compiletest,",
        "  trustc-native, native-contracts-pipeline-v2,",
        "  binary-decompilation-golden, and launch.",
        "  Every canonical release mode remains blocked until its documented",
        "  packaged/provenance/proof evidence has independently authenticated,",
        "  isolated execution authority.",
        "  Smoke aliases cannot cover those canonical inventory IDs; ignored",
        "  receipts cannot grant authority either.",
    ]
    .join("\n")
        + "\n"
}

fn repo_root_from_manifest() -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    root.canonicalize().unwrap_or(root)
}

fn repo_root_for_upstream_tests() -> PathBuf {
    if let Ok(configured) = env::var("TRUST_UPSTREAM_COMPAT_REPO_ROOT") {
        if !configured.trim().is_empty() {
            let root = PathBuf::from(configured);
            return root.canonicalize().unwrap_or(root);
        }
    }

    let manifest_root = repo_root_from_manifest();
    env::current_dir()
        .ok()
        .and_then(|cwd| repo_root_from_git_or_manifest_with_cwd(&cwd, &manifest_root))
        .unwrap_or(manifest_root)
}

fn repo_root_from_git_or_manifest_with_cwd(cwd: &Path, manifest_root: &Path) -> Option<PathBuf> {
    let git = crate::trust_added::resolve_gate_git(manifest_root, false).ok()?;
    let mut command = crate::trust_added::gate_git_command(&git, cwd);
    command.args(["rev-parse", "--show-toplevel"]);
    let output = crate::bounded_process::output(
        &mut command,
        "active repository root probe",
        IDENTITY_PROBE_MAX_STREAM_BYTES,
        IDENTITY_PROBE_TIMEOUT,
    )
    .ok()?;
    if !output.status.success() {
        return None;
    }
    let root = PathBuf::from(strict_single_output_line(output.stdout, "git repository root").ok()?);
    if !root.is_absolute() {
        return None;
    }
    let root = root.canonicalize().ok()?;
    if root == manifest_root || root.join(UPSTREAM_COMPAT_MANIFEST).is_file() {
        Some(root)
    } else {
        None
    }
}

#[derive(Debug, Clone, Default)]
struct UpstreamCompatCargoProbe {
    configured: Option<String>,
    repo_stage2_targo: Option<PathBuf>,
    path_targo: Option<PathBuf>,
}

fn resolve_upstream_compat_cargo(root: &Path, require_trust_cargo: bool) -> Result<Vec<String>> {
    resolve_upstream_compat_cargo_from_probe(
        root,
        require_trust_cargo,
        upstream_compat_cargo_probe(root),
    )
}

fn upstream_compat_cargo_probe(root: &Path) -> UpstreamCompatCargoProbe {
    UpstreamCompatCargoProbe {
        configured: env::var("TRUST_UPSTREAM_COMPAT_CARGO").ok(),
        repo_stage2_targo: find_repo_stage2_targo(root),
        path_targo: which("targo"),
    }
}

fn resolve_upstream_compat_cargo_from_probe(
    root: &Path,
    require_trust_cargo: bool,
    probe: UpstreamCompatCargoProbe,
) -> Result<Vec<String>> {
    if let Some(configured) = probe.configured {
        let command = split_words(&configured);
        if command.is_empty() {
            bail!("TRUST_UPSTREAM_COMPAT_CARGO is empty");
        }
        require_trust_cargo_command(
            root,
            &command,
            "TRUST_UPSTREAM_COMPAT_CARGO",
            require_trust_cargo,
        )?;
        return Ok(command);
    }

    if let Some(stage2) = probe.repo_stage2_targo {
        validate_targo_path(&stage2, "repo-local stage2 targo")?;
        if require_trust_cargo {
            validate_release_stage2_targo(root, &stage2, "repo-local stage2 targo")?;
        }
        return Ok(vec![stage2.to_string_lossy().into_owned()]);
    }

    if let Some(targo) = probe.path_targo {
        validate_targo_path(&targo, "PATH targo")?;
        if require_trust_cargo {
            bail!(
                "release upstream porting requires repo-local stage2 targo; refusing PATH targo {}",
                targo.display()
            );
        }
        return Ok(vec![targo.to_string_lossy().into_owned()]);
    }

    let mode = if require_trust_cargo { "release" } else { "developer" };
    bail!(
        "{mode} upstream porting requires canonical Trust targo; build build/<host>/stage2/bin/targo or select a Trust toolchain on PATH"
    )
}

fn split_words(value: &str) -> Vec<String> {
    value.split_whitespace().map(str::to_string).collect()
}

fn root_path(root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() { path.to_path_buf() } else { root.join(path) }
}

fn require_trust_cargo_command(
    root: &Path,
    command: &[String],
    source: &str,
    require_release_stage2: bool,
) -> Result<()> {
    if let Some(first) = command.first() {
        let path = Path::new(first);
        if is_targo_path(path) {
            if path.is_absolute() || path.components().count() > 1 {
                let resolved = root_path(root, path);
                validate_targo_path(&resolved, source)?;
                if require_release_stage2 {
                    validate_release_stage2_targo(root, &resolved, source)?;
                }
            } else if require_release_stage2 {
                bail!(
                    "release upstream porting requires repo-local stage2 targo; {source} used PATH selector `{first}`"
                );
            }
            return Ok(());
        }
    }

    bail!(
        "upstream porting requires Trust targo; {source} must name canonical targo, not cargo or inherited selectors"
    )
}

fn validate_targo_path(path: &Path, source: &str) -> Result<()> {
    if !is_targo_path(path) {
        bail!("{source} must point to a targo binary: {}", path.display());
    }
    if !is_executable_file(path) {
        bail!("{source} is not executable: {}", path.display());
    }
    Ok(())
}

fn validate_release_stage2_targo(root: &Path, path: &Path, source: &str) -> Result<()> {
    let canonical_targo = path.canonicalize().unwrap_or_else(|_| root_path(root, path));
    if !is_repo_stage2_tool(root, &canonical_targo, targo_binary_name()) {
        bail!(
            "{source} must point at repo-local stage2 targo under build/<host>/stage2/bin/{}: {}",
            targo_binary_name(),
            path.display()
        );
    }
    let bin_dir = canonical_targo
        .parent()
        .with_context(|| format!("{source} has no parent bin directory: {}", path.display()))?;
    let trustc = bin_dir.join(trustc_binary_name());
    if !is_executable_file(&trustc) {
        bail!(
            "release upstream porting requires sibling stage2 trustc next to targo: {}",
            trustc.display()
        );
    }
    let repo_head = current_git_head(root)?;
    let trustc_commit = trustc_commit_hash(&trustc)?;
    if trustc_commit != repo_head {
        bail!(
            "release upstream porting refuses stale stage2 trustc: {} reports commit-hash {}, expected current HEAD {}; rebuild with ./x.py build --stage 2 compiler/rustc",
            trustc.display(),
            trustc_commit,
            repo_head
        );
    }
    Ok(())
}

fn is_repo_stage2_tool(root: &Path, path: &Path, expected_name: &str) -> bool {
    let canonical_path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let canonical_root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    let Ok(relative) = canonical_path.strip_prefix(&canonical_root) else {
        return false;
    };
    let components = relative
        .components()
        .filter_map(|component| match component {
            Component::Normal(value) => value.to_str(),
            _ => None,
        })
        .collect::<Vec<_>>();
    components.len() == 5
        && components[0] == "build"
        && components[2] == "stage2"
        && components[3] == "bin"
        && components[4] == expected_name
}

fn current_git_head(root: &Path) -> Result<String> {
    crate::controlled_git::canonical_head(
        root,
        "current repository HEAD probe",
        IDENTITY_PROBE_MAX_STREAM_BYTES,
        IDENTITY_PROBE_TIMEOUT,
    )
    .map_err(anyhow::Error::msg)
    .with_context(|| format!("failed to read current git HEAD under {}", root.display()))
}

fn trustc_commit_hash(trustc: &Path) -> Result<String> {
    let mut command = Command::new(trustc);
    command.arg("-Vv");
    let output = crate::bounded_process::output(
        &mut command,
        "stage2 trustc identity probe",
        IDENTITY_PROBE_MAX_STREAM_BYTES,
        IDENTITY_PROBE_TIMEOUT,
    )
    .map_err(anyhow::Error::msg)
    .with_context(|| format!("failed to run {} -Vv", trustc.display()))?;
    if !output.status.success() {
        bail!(
            "stage2 trustc -Vv failed for {}\nstdout:\n{}\nstderr:\n{}",
            trustc.display(),
            command_output_text(&output.stdout),
            command_output_text(&output.stderr)
        );
    }
    let stdout = String::from_utf8(output.stdout)
        .with_context(|| format!("{} -Vv stdout was not valid UTF-8", trustc.display()))?;
    let stderr = String::from_utf8(output.stderr)
        .with_context(|| format!("{} -Vv stderr was not valid UTF-8", trustc.display()))?;
    let version_text = format!("{stdout}\n{stderr}");
    let commits = version_text
        .lines()
        .filter_map(|line| line.trim().strip_prefix("commit-hash:").map(str::trim))
        .filter(|value| !value.is_empty())
        .collect::<Vec<_>>();
    let [commit] = commits.as_slice() else {
        bail!(
            "{} -Vv must report exactly one commit-hash field, observed {}",
            trustc.display(),
            commits.len()
        );
    };
    let commit = (*commit).to_string();
    if !is_full_git_sha(&commit) {
        bail!("{} -Vv reported non-40-hex commit-hash `{commit}`", trustc.display());
    }
    Ok(commit)
}

fn strict_single_output_line(bytes: Vec<u8>, context: &str) -> Result<String> {
    let text =
        String::from_utf8(bytes).with_context(|| format!("{context} was not valid UTF-8"))?;
    let text = text.strip_suffix('\n').unwrap_or(&text);
    let text = text.strip_suffix('\r').unwrap_or(text);
    if text.is_empty() || text.contains('\r') || text.contains('\n') {
        bail!("{context} must contain exactly one nonempty line");
    }
    Ok(text.to_string())
}

fn is_executable_file(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::metadata(path)
            .map(|metadata| metadata.permissions().mode() & 0o111 != 0)
            .unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn find_repo_stage2_targo(root: &Path) -> Option<PathBuf> {
    let direct = root.join("build/host/stage2/bin").join(targo_binary_name());
    if is_executable_file(&direct) {
        return Some(direct);
    }
    let mut host_dirs = fs::read_dir(root.join("build"))
        .ok()?
        .flatten()
        .map(|entry| entry.path())
        .collect::<Vec<_>>();
    host_dirs.sort();
    for entry in host_dirs {
        let candidate = entry.join("stage2/bin").join(targo_binary_name());
        if is_executable_file(&candidate) {
            return Some(candidate);
        }
    }
    None
}

fn trustc_binary_name() -> &'static str {
    if cfg!(windows) { "trustc.exe" } else { "trustc" }
}

fn which(name: &str) -> Option<PathBuf> {
    let paths = env::var_os("PATH")?;
    for dir in env::split_paths(&paths) {
        let candidate = dir.join(name);
        if is_executable_file(&candidate) {
            return Some(candidate);
        }
    }
    None
}

fn targo_binary_name() -> &'static str {
    // Trust: produced canonical Cargo frontend is `targo`.
    if cfg!(windows) { "targo.exe" } else { "targo" }
}

fn is_targo_path(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name == "targo" || name == "targo.exe")
}

fn parse_args(args: &[String]) -> Result<RustVsTrustArgs> {
    let mut parsed = RustVsTrustArgs {
        format: OutputFormat::Terminal,
        suite: None,
        compat_summary: Vec::new(),
        proof_program_index_report: None,
        proof_unsafe_memory_report: None,
        proof_concurrency_report: None,
        program_index_benchmark_report: Vec::new(),
        product_proof_release_report: None,
        out: None,
        write_template: None,
        allow_missing_evidence: false,
        allow_exceptions: false,
        min_performance_advantage_pct: None,
    };

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--json" => parsed.format = OutputFormat::Json,
            "--format" => {
                i += 1;
                let value = args.get(i).context("--format requires a value")?;
                parsed.format = OutputFormat::from_str(value)?;
            }
            value if value.starts_with("--format=") => {
                let value = value.strip_prefix("--format=").expect("prefix checked");
                parsed.format = OutputFormat::from_str(value)?;
            }
            "--suite" => {
                i += 1;
                parsed.suite = Some(PathBuf::from(args.get(i).context("--suite requires a path")?));
            }
            value if value.starts_with("--suite=") => {
                parsed.suite =
                    Some(PathBuf::from(value.strip_prefix("--suite=").expect("prefix checked")));
            }
            "--compat-summary" => {
                i += 1;
                parsed
                    .compat_summary
                    .push(PathBuf::from(args.get(i).context("--compat-summary requires a path")?));
            }
            value if value.starts_with("--compat-summary=") => {
                parsed.compat_summary.push(PathBuf::from(
                    value.strip_prefix("--compat-summary=").expect("prefix checked"),
                ));
            }
            "--proof-program-index-report" => {
                i += 1;
                parsed.proof_program_index_report = Some(PathBuf::from(
                    args.get(i).context("--proof-program-index-report requires a path")?,
                ));
            }
            value if value.starts_with("--proof-program-index-report=") => {
                parsed.proof_program_index_report = Some(PathBuf::from(
                    value.strip_prefix("--proof-program-index-report=").expect("prefix checked"),
                ));
            }
            PROOF_UNSAFE_MEMORY_REPORT_FLAG => {
                i += 1;
                parsed.proof_unsafe_memory_report =
                    Some(PathBuf::from(args.get(i).with_context(|| {
                        format!("{PROOF_UNSAFE_MEMORY_REPORT_FLAG} requires a path")
                    })?));
            }
            value
                if value
                    .strip_prefix(PROOF_UNSAFE_MEMORY_REPORT_FLAG)
                    .and_then(|rest| rest.strip_prefix('='))
                    .is_some() =>
            {
                parsed.proof_unsafe_memory_report = Some(PathBuf::from(
                    value
                        .strip_prefix(PROOF_UNSAFE_MEMORY_REPORT_FLAG)
                        .and_then(|rest| rest.strip_prefix('='))
                        .expect("prefix checked"),
                ));
            }
            PROOF_CONCURRENCY_REPORT_FLAG => {
                i += 1;
                parsed.proof_concurrency_report =
                    Some(PathBuf::from(args.get(i).with_context(|| {
                        format!("{PROOF_CONCURRENCY_REPORT_FLAG} requires a path")
                    })?));
            }
            value
                if value
                    .strip_prefix(PROOF_CONCURRENCY_REPORT_FLAG)
                    .and_then(|rest| rest.strip_prefix('='))
                    .is_some() =>
            {
                parsed.proof_concurrency_report = Some(PathBuf::from(
                    value
                        .strip_prefix(PROOF_CONCURRENCY_REPORT_FLAG)
                        .and_then(|rest| rest.strip_prefix('='))
                        .expect("prefix checked"),
                ));
            }
            PROGRAM_INDEX_BENCHMARK_REPORT_FLAG => {
                i += 1;
                parsed.program_index_benchmark_report.push(PathBuf::from(
                    args.get(i).with_context(|| {
                        format!("{PROGRAM_INDEX_BENCHMARK_REPORT_FLAG} requires a path")
                    })?,
                ));
            }
            value
                if value
                    .strip_prefix(PROGRAM_INDEX_BENCHMARK_REPORT_FLAG)
                    .and_then(|rest| rest.strip_prefix('='))
                    .is_some() =>
            {
                parsed.program_index_benchmark_report.push(PathBuf::from(
                    value
                        .strip_prefix(PROGRAM_INDEX_BENCHMARK_REPORT_FLAG)
                        .and_then(|rest| rest.strip_prefix('='))
                        .expect("prefix checked"),
                ));
            }
            PRODUCT_PROOF_RELEASE_REPORT_FLAG => {
                i += 1;
                parsed.product_proof_release_report =
                    Some(PathBuf::from(args.get(i).with_context(|| {
                        format!("{PRODUCT_PROOF_RELEASE_REPORT_FLAG} requires a path")
                    })?));
            }
            value
                if value
                    .strip_prefix(PRODUCT_PROOF_RELEASE_REPORT_FLAG)
                    .and_then(|rest| rest.strip_prefix('='))
                    .is_some() =>
            {
                parsed.product_proof_release_report = Some(PathBuf::from(
                    value
                        .strip_prefix(PRODUCT_PROOF_RELEASE_REPORT_FLAG)
                        .and_then(|rest| rest.strip_prefix('='))
                        .expect("prefix checked"),
                ));
            }
            "--out" => {
                i += 1;
                parsed.out = Some(PathBuf::from(args.get(i).context("--out requires a path")?));
            }
            value if value.starts_with("--out=") => {
                parsed.out =
                    Some(PathBuf::from(value.strip_prefix("--out=").expect("prefix checked")));
            }
            "--write-template" => {
                i += 1;
                parsed.write_template =
                    Some(PathBuf::from(args.get(i).context("--write-template requires a path")?));
            }
            value if value.starts_with("--write-template=") => {
                parsed.write_template = Some(PathBuf::from(
                    value.strip_prefix("--write-template=").expect("prefix checked"),
                ));
            }
            "--allow-missing-evidence" => parsed.allow_missing_evidence = true,
            "--allow-exceptions" => parsed.allow_exceptions = true,
            "--min-performance-advantage-pct" => {
                i += 1;
                let value = args
                    .get(i)
                    .context("--min-performance-advantage-pct requires a numeric value")?;
                parsed.min_performance_advantage_pct =
                    Some(parse_pct("--min-performance-advantage-pct", value)?);
            }
            value if value.starts_with("--min-performance-advantage-pct=") => {
                let value =
                    value.strip_prefix("--min-performance-advantage-pct=").expect("prefix checked");
                parsed.min_performance_advantage_pct =
                    Some(parse_pct("--min-performance-advantage-pct", value)?);
            }
            other => bail!("domination: unexpected argument `{other}`"),
        }
        i += 1;
    }

    Ok(parsed)
}

fn parse_pct(flag: &str, value: &str) -> Result<f64> {
    let parsed = value.parse::<f64>().with_context(|| format!("{flag} must be numeric"))?;
    if parsed < 0.0 {
        bail!("{flag} must be non-negative");
    }
    Ok(parsed)
}

fn write_template(path: &Path) -> Result<()> {
    if path == Path::new("-") {
        print!("{TEMPLATE}");
        return Ok(());
    }

    fs::write(path, TEMPLATE).with_context(|| format!("failed to write {}", path.display()))
}

fn build_report(args: &RustVsTrustArgs) -> Result<RustVsTrustReport> {
    let mut policy = EffectivePolicy::from_input(&PolicyInput::default());
    let mut dimensions = Vec::new();
    let mut compat_ingest = None;
    let mut evidence_commit_bindings = Vec::new();
    let mut compat_arch_claims = Vec::new();

    let suite_id = if let Some(path) = args.suite.as_deref() {
        let suite = read_suite(path)?;
        if suite.schema_version != SUITE_SCHEMA_VERSION {
            bail!(
                "suite {} has schema_version `{}`, expected `{}`",
                path.display(),
                suite.schema_version,
                SUITE_SCHEMA_VERSION
            );
        }
        let suite_id = suite.suite_id.clone();
        policy = EffectivePolicy::from_input(&suite.policy);
        dimensions.extend(suite.dimensions);
        suite_id
    } else {
        dimensions.extend(default_launch_dimensions());
        Some("trust-total-domination-default".to_string())
    };

    if args.allow_missing_evidence {
        policy.require_evidence_for_required = false;
    }
    if args.allow_exceptions {
        policy.allow_exceptions = true;
    }
    if let Some(min_performance_advantage_pct) = args.min_performance_advantage_pct {
        policy.min_performance_advantage_pct = min_performance_advantage_pct;
    }

    for path in &args.compat_summary {
        let (compat_dimensions, ingest) = read_compat_summary(path, policy.allow_exceptions)?;
        compat_arch_claims.push(read_compat_summary_arch_claim(path)?);
        if let Some(binding) = read_compat_summary_commit_binding(path)? {
            evidence_commit_bindings.push(binding);
        }
        merge_compat_ingest(&mut compat_ingest, ingest);
        for dimension in compat_dimensions {
            upsert_dimension(&mut dimensions, dimension);
        }
    }

    if let Some(path) = args.proof_program_index_report.as_deref() {
        let proof_dimension = read_proof_functional_program_index_report(path)?;
        if let Some(binding) =
            read_json_commit_binding(path, "proof-program-index-report", "repo_head")?
        {
            evidence_commit_bindings.push(binding);
        }
        upsert_dimension(&mut dimensions, proof_dimension);
    }
    if let Some(path) = args.proof_unsafe_memory_report.as_deref() {
        let proof_dimension = read_proof_unsafe_memory_report(path)?;
        if let Some(binding) =
            read_json_commit_binding(path, "proof-unsafe-memory-report", "candidate_commit")?
        {
            evidence_commit_bindings.push(binding);
        }
        upsert_dimension(&mut dimensions, proof_dimension);
    }
    if let Some(path) = args.proof_concurrency_report.as_deref() {
        let proof_dimension = read_proof_concurrency_report(path)?;
        if let Some(binding) =
            read_json_commit_binding(path, "proof-concurrency-report", "repo_head")?
        {
            evidence_commit_bindings.push(binding);
        }
        upsert_dimension(&mut dimensions, proof_dimension);
    }
    for path in &args.program_index_benchmark_report {
        for dimension in read_program_index_runtime_binary_report(path)? {
            upsert_dimension(&mut dimensions, dimension);
        }
        if let Some(binding) =
            read_json_commit_binding(path, "program-index-benchmark-report", "repo_head")?
        {
            evidence_commit_bindings.push(binding);
        }
    }
    if let Some(path) = args.product_proof_release_report.as_deref() {
        let dimension = read_product_proof_release_report(path)?;
        if let Some(binding) =
            read_json_commit_binding(path, "product-proof-release-report", "candidate_commit")?
        {
            evidence_commit_bindings.push(binding);
        }
        upsert_dimension(&mut dimensions, dimension);
    }

    let mut extra_blockers = evidence_commit_consistency_blockers(&evidence_commit_bindings);
    extra_blockers.extend(compat_summary_arch_coverage_blockers(&compat_arch_claims));

    Ok(evaluate_suite_with_extra_blockers(
        suite_id,
        policy,
        dimensions,
        compat_ingest,
        extra_blockers,
    ))
}

fn read_suite(path: &Path) -> Result<SuiteInput> {
    let content = read_bounded_utf8_file(path, MAX_RELEASE_METADATA_BYTES)
        .with_context(|| format!("failed to read {} safely", path.display()))?;
    if is_json_path(path) {
        serde_json::from_str(&content)
            .with_context(|| format!("failed to parse JSON suite {}", path.display()))
    } else {
        toml::from_str(&content)
            .with_context(|| format!("failed to parse TOML suite {}", path.display()))
    }
}

fn parse_compat_summary(path: &Path) -> Result<CompatibilityResultSummaryInput> {
    let content = read_bounded_utf8_file(path, MAX_SAVED_PROOF_REPORT_BYTES)
        .with_context(|| format!("failed to read {} safely", path.display()))?;
    if is_json_path(path) {
        serde_json::from_str(&content).with_context(|| {
            format!("failed to parse JSON compatibility summary {}", path.display())
        })
    } else {
        toml::from_str(&content).with_context(|| {
            format!("failed to parse TOML compatibility summary {}", path.display())
        })
    }
}

fn read_compat_summary_commit_binding(path: &Path) -> Result<Option<EvidenceCommitBinding>> {
    let summary = parse_compat_summary(path)?;
    Ok(summary.repo_head.and_then(|commit| {
        is_full_git_sha(&commit).then(|| EvidenceCommitBinding::new("compat-summary", path, commit))
    }))
}

fn read_json_commit_binding(
    path: &Path,
    source: &'static str,
    field: &str,
) -> Result<Option<EvidenceCommitBinding>> {
    let content = read_bounded_utf8_file(path, MAX_SAVED_PROOF_REPORT_BYTES)
        .with_context(|| format!("failed to read {} safely", path.display()))?;
    let report: Value = serde_json::from_str(&content)
        .with_context(|| format!("failed to parse JSON evidence report {}", path.display()))?;
    Ok(value_at(&report, field).and_then(|commit| {
        is_full_git_sha(commit)
            .then(|| EvidenceCommitBinding::new(source, path, commit.to_string()))
    }))
}

fn evidence_commit_consistency_blockers(bindings: &[EvidenceCommitBinding]) -> Vec<Blocker> {
    let Some(expected) = bindings.first().map(|binding| binding.commit.as_str()) else {
        return Vec::new();
    };
    if bindings.iter().all(|binding| binding.commit == expected) {
        return Vec::new();
    }

    let observed = bindings
        .iter()
        .map(|binding| format!("{} {}={}", binding.source, binding.path, binding.commit))
        .collect::<Vec<_>>()
        .join("; ");
    vec![Blocker {
        severity: Severity::P0,
        kind: BlockerKind::InconsistentEvidence,
        dimension_id: None,
        message: "evidence reports bind different reviewed commits".to_string(),
        action: format!(
            "Regenerate every Rust-vs-Trust evidence artifact on one clean reviewed commit. Observed: {observed}"
        ),
    }]
}

fn read_compat_summary(
    path: &Path,
    allow_exceptions: bool,
) -> Result<(Vec<DimensionInput>, CompatSummaryIngestReport)> {
    let summary = parse_compat_summary(path)?;

    if summary.schema_version != UPSTREAM_COMPAT_SUMMARY_SCHEMA_VERSION {
        bail!(
            "compatibility summary {} has schema_version `{}`, expected `{}`",
            path.display(),
            summary.schema_version,
            UPSTREAM_COMPAT_SUMMARY_SCHEMA_VERSION
        );
    }
    validate_compat_summary_provenance(path, &summary)?;

    let Some(declared_totals) = summary.totals else {
        bail!("compatibility summary {} must declare totals", path.display());
    };
    let computed_totals = CompatibilityResultTotalsInput::from_results(&summary.results);
    if declared_totals != computed_totals {
        bail!(
            "compatibility summary {} declares totals {:?}, but computed {:?} from result rows",
            path.display(),
            declared_totals,
            computed_totals
        );
    }

    let mut compatible = 0;
    let mut non_compatible = 0;
    let mut unknown = 0;
    let mut aggregate_passed = 0_u64;
    let mut aggregate_failed = 0_u64;
    let mut aggregate_unknown = 0_u64;
    let mut dimensions = Vec::new();
    let aggregate_arch = compatibility_summary_arch(&summary);

    for row in summary.results {
        let (status, title, hint) = match row.outcome {
            CompatibilityOutcomeInput::Compatible => {
                compatible += 1;
                (
                    DeclaredStatus::Pass,
                    format!("{} compatibility", row.baseline_entry_id),
                    "Keep this compatibility row green on every reviewed commit.".to_string(),
                )
            }
            CompatibilityOutcomeInput::Unknown => {
                unknown += 1;
                (
                    DeclaredStatus::Unknown,
                    format!("{} compatibility unknown", row.baseline_entry_id),
                    "Run or repair the upstream Rust compatibility gate until this row is classified."
                        .to_string(),
                )
            }
            CompatibilityOutcomeInput::Excepted if allow_exceptions => {
                non_compatible += 1;
                (
                    DeclaredStatus::Pass,
                    format!("{} compatibility excepted", row.baseline_entry_id),
                    "Draft mode accepted this exception; remove it before public superiority claims."
                        .to_string(),
                )
            }
            CompatibilityOutcomeInput::Excepted => {
                non_compatible += 1;
                (
                    DeclaredStatus::Fail,
                    format!("{} compatibility excepted", row.baseline_entry_id),
                    format!(
                        "Eliminate exception {} and make this row compatible.",
                        row.exception_id.as_deref().unwrap_or("<missing exception id>")
                    ),
                )
            }
            CompatibilityOutcomeInput::FixedUpstream => {
                non_compatible += 1;
                (
                    DeclaredStatus::Fail,
                    format!("{} upstream drift", row.baseline_entry_id),
                    format!(
                        "Rebase or port upstream fix {} and regenerate the compatibility baseline.",
                        row.upstream_fix_id.as_deref().unwrap_or("<missing upstream fix id>")
                    ),
                )
            }
            CompatibilityOutcomeInput::Divergent => {
                non_compatible += 1;
                (
                    DeclaredStatus::Fail,
                    format!("{} divergent", row.baseline_entry_id),
                    "Remove this Rust compatibility divergence or provide a non-replacement claim."
                        .to_string(),
                )
            }
        };
        match status {
            DeclaredStatus::Pass => aggregate_passed += 1,
            DeclaredStatus::Fail => aggregate_failed += 1,
            DeclaredStatus::Unknown => aggregate_unknown += 1,
        }

        let hint = compat_summary_hint(hint, row.observed.as_deref());
        let observed = row
            .observed
            .as_deref()
            .map(str::trim)
            .filter(|observed| !observed.is_empty())
            .map(str::to_string)
            .unwrap_or_else(|| format!("outcome={:?}", row.outcome));
        dimensions.push(DimensionInput {
            id: format!("compat.{}", row.baseline_entry_id),
            title,
            category: DimensionCategory::Compatibility,
            metric: Some(MetricKind::PassRate),
            comparison_baseline: Some("adopted upstream Rust snapshot".to_string()),
            required: true,
            rust_value: None,
            trust_value: None,
            higher_is_better: Some(true),
            min_trust_delta_pct: None,
            max_trust_regression_pct: None,
            status: Some(status),
            unit: Some("compatibility_row".to_string()),
            weight: 1.0,
            evidence: vec![format!("{}: {observed}", path.display())],
            ai_hint: Some(hint),
            owner: None,
            evidence_source: DimensionEvidenceSource::Manual,
        });
    }

    if let Some(arch) = aggregate_arch {
        dimensions.push(compatibility_aggregate_dimension(
            path,
            arch,
            aggregate_passed,
            aggregate_failed,
            aggregate_unknown,
        ));
    }

    let ingest = CompatSummaryIngestReport {
        path: path.display().to_string(),
        rows: compatible + non_compatible + unknown,
        compatible,
        non_compatible,
        unknown,
        exceptions_rejected: !allow_exceptions,
    };

    Ok((dimensions, ingest))
}

#[derive(Debug, Clone)]
struct CompatSummaryArchClaim {
    path: String,
    target_arch: Option<String>,
    status: CompatSummaryTargetArchStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompatSummaryTargetArchStatus {
    Missing,
    AmbiguousOrUnsupported,
    Accepted(LaunchArch),
}

fn read_compat_summary_arch_claim(path: &Path) -> Result<CompatSummaryArchClaim> {
    let summary = parse_compat_summary(path)?;
    Ok(compat_summary_arch_claim(path, &summary))
}

fn compat_summary_arch_claim(
    path: &Path,
    summary: &CompatibilityResultSummaryInput,
) -> CompatSummaryArchClaim {
    let target_arch = summary
        .target_arch
        .as_deref()
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(str::to_string);
    let status = match target_arch.as_deref() {
        Some(value) => compat_target_arch_from_text(value)
            .map(CompatSummaryTargetArchStatus::Accepted)
            .unwrap_or(CompatSummaryTargetArchStatus::AmbiguousOrUnsupported),
        None => CompatSummaryTargetArchStatus::Missing,
    };
    CompatSummaryArchClaim { path: path.display().to_string(), target_arch, status }
}

fn compat_summary_arch_coverage_blockers(claims: &[CompatSummaryArchClaim]) -> Vec<Blocker> {
    if claims.is_empty() {
        return Vec::new();
    }

    let mut blockers = Vec::new();
    let mut aarch64_paths = Vec::new();
    let mut x86_64_paths = Vec::new();

    for claim in claims {
        match claim.status {
            CompatSummaryTargetArchStatus::Accepted(LaunchArch::Aarch64) => {
                aarch64_paths.push(claim.path.as_str());
            }
            CompatSummaryTargetArchStatus::Accepted(LaunchArch::X86_64) => {
                x86_64_paths.push(claim.path.as_str());
            }
            CompatSummaryTargetArchStatus::Missing => {
                blockers.push(compat_arch_coverage_blocker(
                    None,
                    format!(
                        "release-grade upstream compatibility summary {} must declare explicit target_arch",
                        claim.path
                    ),
                    "Regenerate this summary with `targo trust domination upstream-tests --release --target-arch x86_64` or `--target-arch aarch64`; legacy host, target, baseline_id, or run_id inference is not admissible release evidence."
                        .to_string(),
                ));
            }
            CompatSummaryTargetArchStatus::AmbiguousOrUnsupported => {
                let target_arch = claim.target_arch.as_deref().unwrap_or("<missing>");
                blockers.push(compat_arch_coverage_blocker(
                    None,
                    format!(
                        "release-grade upstream compatibility summary {} has unsupported or ambiguous target_arch `{target_arch}`",
                        claim.path
                    ),
                    "Regenerate this summary with an unambiguous `target_arch` of `x86_64`, `aarch64`, or `AArch64`."
                        .to_string(),
                ));
            }
        }
    }

    blockers.extend(required_compat_arch_blockers(LaunchArch::Aarch64, &aarch64_paths));
    blockers.extend(required_compat_arch_blockers(LaunchArch::X86_64, &x86_64_paths));
    blockers
}

fn required_compat_arch_blockers(arch: LaunchArch, paths: &[&str]) -> Vec<Blocker> {
    match paths.len() {
        0 => vec![compat_arch_coverage_blocker(
            Some(arch),
            format!(
                "release-grade upstream compatibility evidence is missing a {} target_arch summary",
                arch.label()
            ),
            format!(
                "Run `targo trust domination upstream-tests --release --target-arch {}` and pass the generated compat summary with --compat-summary.",
                arch.evidence_token()
            ),
        )],
        1 => Vec::new(),
        _ => vec![compat_arch_coverage_blocker(
            Some(arch),
            format!(
                "release-grade upstream compatibility evidence has duplicate {} target_arch summaries",
                arch.label()
            ),
            format!(
                "Keep exactly one {} compat summary. Observed: {}.",
                arch.evidence_token(),
                paths.join(", ")
            ),
        )],
    }
}

fn compat_arch_coverage_blocker(
    arch: Option<LaunchArch>,
    message: String,
    action: String,
) -> Blocker {
    Blocker {
        severity: Severity::P0,
        kind: BlockerKind::CompatibilityNotProven,
        dimension_id: arch.map(|arch| arch.compat_dimension_id().to_string()),
        message,
        action,
    }
}

fn merge_compat_ingest(
    aggregate: &mut Option<CompatSummaryIngestReport>,
    ingest: CompatSummaryIngestReport,
) {
    match aggregate {
        Some(existing) => {
            existing.path = format!("{}, {}", existing.path, ingest.path);
            existing.rows += ingest.rows;
            existing.compatible += ingest.compatible;
            existing.non_compatible += ingest.non_compatible;
            existing.unknown += ingest.unknown;
            existing.exceptions_rejected &= ingest.exceptions_rejected;
        }
        None => *aggregate = Some(ingest),
    }
}

fn validate_compat_summary_provenance(
    path: &Path,
    summary: &CompatibilityResultSummaryInput,
) -> Result<()> {
    let mut blockers = Vec::new();
    if !summary.generated_on.as_deref().is_some_and(|value| !value.is_empty()) {
        blockers.push("generated_on must be present".to_string());
    }
    if !summary.run_id.as_deref().is_some_and(|value| !value.is_empty()) {
        blockers.push("run_id must be present".to_string());
    }
    match summary.repo_head.as_deref() {
        Some(head) if is_full_git_sha(head) => {}
        Some(head) => blockers.push(format!("repo_head must be a full git SHA, got `{head}`")),
        None => blockers.push("repo_head must be present".to_string()),
    }
    match summary.repo_dirty {
        Some(false) => {}
        Some(true) => blockers.push("repo_dirty must be false".to_string()),
        None => blockers.push("repo_dirty=false must be present".to_string()),
    }
    match summary.upstream_revision.as_deref() {
        Some(revision) if text_contains_full_git_sha(revision) => {}
        Some(revision) => blockers
            .push(format!("upstream_revision must include a full git SHA, got `{revision}`")),
        None => blockers.push("upstream_revision must be present".to_string()),
    }
    match summary.runner.as_ref() {
        Some(runner)
            if compatibility_runner_is_trust_owned(runner)
                && compatibility_runner_declares_release_argv(runner)
                && compatibility_runner_release_contract_satisfied(runner) => {}
        Some(_) => blockers.push(
            "runner must declare python_used=false, a Rust-owned trust-upstream-compat entrypoint, release argv with --release --proof-mode full --execute --summary-out, and release_evidence_contract.satisfied=true"
                .to_string(),
        ),
        None => blockers.push("runner must be present".to_string()),
    }

    if blockers.is_empty() {
        Ok(())
    } else {
        bail!(
            "compatibility summary {} lacks proof-grade provenance: {}",
            path.display(),
            blockers.join("; ")
        )
    }
}

fn compatibility_runner_is_trust_owned(runner: &Value) -> bool {
    trust_runner_is_trust_owned(runner, TrustRunnerEntrypoint::UpstreamCompat)
}

fn compatibility_runner_declares_release_argv(runner: &Value) -> bool {
    let mut tokens = Vec::new();
    for key in ["command", "command_line", "argv", "args"] {
        if let Some(value) = runner.get(key) {
            collect_runner_command_tokens(value, &mut tokens);
        }
    }
    if tokens.is_empty() {
        return false;
    }
    tokens_contain_sequence(&tokens, &["--release"])
        && tokens_contain_sequence(&tokens, &["--proof-mode", "full"])
        && tokens_contain_sequence(&tokens, &["--execute"])
        && tokens_contain_sequence(&tokens, &["--summary-out"])
        && !tokens_contain_sequence(&tokens, &["--no-execute"])
        && !tokens_contain_sequence(&tokens, &["--max-files"])
}

fn compatibility_runner_release_contract_satisfied(runner: &Value) -> bool {
    let contract = runner.get("release_evidence_contract").unwrap_or(&Value::Null);
    contract.get("satisfied").and_then(Value::as_bool) == Some(true)
        && contract.get("requires_release").and_then(Value::as_bool) == Some(true)
        && contract.get("requires_execute").and_then(Value::as_bool) == Some(true)
        && contract.get("requires_summary_out").and_then(Value::as_bool) == Some(true)
        && value_at(contract, "requires_proof_mode") == Some("full")
        && contract.get("release").and_then(Value::as_bool) == Some(true)
        && contract.get("execute").and_then(Value::as_bool) == Some(true)
        && value_at(contract, "proof_mode") == Some("full")
        && value_at(contract, "summary_out").is_some_and(|value| !value.trim().is_empty())
}

#[derive(Clone, Copy)]
enum TrustRunnerEntrypoint {
    UpstreamCompat,
    ProductProofRelease,
}

fn trust_runner_is_trust_owned(runner: &Value, entrypoint: TrustRunnerEntrypoint) -> bool {
    runner.get("python_used").and_then(Value::as_bool) == Some(false)
        && !value_declares_python_command_marker(runner)
        && runner_declares_rust_implementation(runner)
        && runner_declares_entrypoint(runner, entrypoint)
}

fn runner_declares_rust_implementation(runner: &Value) -> bool {
    ["implementation", "language", "runtime", "kind", "runner_kind"]
        .iter()
        .filter_map(|key| runner.get(*key))
        .any(value_declares_rust_runner)
}

fn runner_declares_entrypoint(runner: &Value, entrypoint: TrustRunnerEntrypoint) -> bool {
    [
        "identity",
        "entrypoint",
        "command",
        "command_line",
        "argv",
        "args",
        "executable",
        "path",
        "binary",
    ]
    .iter()
    .filter_map(|key| runner.get(*key))
    .any(|value| value_declares_runner_entrypoint(value, entrypoint))
}

fn value_declares_rust_runner(value: &Value) -> bool {
    match value {
        Value::String(text) => text_declares_rust_runner(text),
        Value::Array(values) => values.iter().any(value_declares_rust_runner),
        Value::Object(map) => map.values().any(value_declares_rust_runner),
        _ => false,
    }
}

fn text_declares_rust_runner(text: &str) -> bool {
    matches!(
        text.trim().to_ascii_lowercase().replace('_', "-").as_str(),
        "rust"
            | "native"
            | "rust-native"
            | "trust-native"
            | "rust-owned"
            | "candidate-stage2"
            | "candidate-stage3"
            | "stage2"
            | "stage3"
    )
}

fn value_declares_runner_entrypoint(value: &Value, entrypoint: TrustRunnerEntrypoint) -> bool {
    let mut tokens = Vec::new();
    collect_runner_command_tokens(value, &mut tokens);
    runner_tokens_declare_entrypoint(&tokens, entrypoint)
}

fn collect_runner_command_tokens(value: &Value, out: &mut Vec<String>) {
    match value {
        Value::String(text) => out.extend(command_tokens(text)),
        Value::Array(values) => {
            for value in values {
                collect_runner_command_tokens(value, out);
            }
        }
        Value::Object(map) => {
            for value in map.values() {
                collect_runner_command_tokens(value, out);
            }
        }
        _ => {}
    }
}

fn runner_tokens_declare_entrypoint(tokens: &[String], entrypoint: TrustRunnerEntrypoint) -> bool {
    match entrypoint {
        TrustRunnerEntrypoint::UpstreamCompat => {
            tokens_contain_sequence(tokens, &["targo", "trust", "domination", "upstream-tests"])
                || tokens_contain_sequence(
                    tokens,
                    &["targo-trust", "trust", "domination", "upstream-tests"],
                )
                || tokens_contain_sequence(tokens, &["trust-upstream-compat", "port"])
        }
        TrustRunnerEntrypoint::ProductProofRelease => {
            tokens_contain_sequence(tokens, &["targo", "trust", "release", "check"])
                || tokens_contain_sequence(tokens, &["targo-trust", "trust", "release", "check"])
        }
    }
}

fn tokens_contain_sequence(tokens: &[String], expected: &[&str]) -> bool {
    expected.len() <= tokens.len()
        && tokens
            .windows(expected.len())
            .any(|window| window.iter().zip(expected).all(|(actual, expected)| actual == expected))
}

fn command_tokens(text: &str) -> Vec<String> {
    text.to_ascii_lowercase()
        .replace('_', "-")
        .split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '-'))
        .filter(|token| !token.is_empty())
        .map(str::to_string)
        .collect()
}

fn value_declares_python_command_marker(value: &Value) -> bool {
    match value {
        Value::String(text) => text_declares_python_command_marker(text),
        Value::Array(values) => values.iter().any(value_declares_python_command_marker),
        Value::Object(map) => map.iter().any(|(key, value)| {
            (key.eq_ignore_ascii_case("python_used") && value.as_bool() == Some(true))
                || value_declares_python_command_marker(value)
        }),
        _ => false,
    }
}

fn text_declares_python_command_marker(text: &str) -> bool {
    let lower = text.to_ascii_lowercase().replace('\\', "/");
    if lower.contains(".py") {
        return true;
    }
    lower
        .split(|ch: char| {
            !(ch.is_ascii_alphanumeric() || matches!(ch, '.' | '-' | '_' | '/' | ':' | '"' | '\''))
        })
        .filter(|token| !trim_runner_quotes(token).is_empty())
        .any(|token| {
            let normalized = trim_runner_quotes(token);
            let command = runner_path_basename(normalized)
                .strip_suffix(".exe")
                .unwrap_or_else(|| runner_path_basename(normalized));
            is_python_command_name(command)
        })
}

fn trim_runner_quotes(value: &str) -> &str {
    value.trim_matches(|ch| matches!(ch, '"' | '\''))
}

fn runner_path_basename(value: &str) -> &str {
    value.rsplit(|ch| matches!(ch, '/' | ':')).next().unwrap_or(value)
}

fn is_python_command_name(command: &str) -> bool {
    command == "python"
        || command == "python2"
        || command == "python3"
        || python_versioned_command(command, "python2.")
        || python_versioned_command(command, "python3.")
}

fn python_versioned_command(command: &str, prefix: &str) -> bool {
    command.strip_prefix(prefix).is_some_and(|suffix| {
        !suffix.is_empty() && suffix.chars().all(|ch| ch.is_ascii_digit() || ch == '.')
    })
}

fn compat_summary_hint(mut hint: String, observed: Option<&str>) -> String {
    let Some(observed) = observed.map(str::trim).filter(|observed| !observed.is_empty()) else {
        return hint;
    };
    hint.push_str(" Observed: ");
    hint.push_str(observed);
    hint
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LaunchArch {
    Aarch64,
    X86_64,
}

impl LaunchArch {
    fn compat_dimension_id(self) -> &'static str {
        match self {
            Self::Aarch64 => "compat.aarch64.toolchain",
            Self::X86_64 => "compat.x86_64.toolchain",
        }
    }

    fn runtime_dimension_id(self) -> &'static str {
        match self {
            Self::Aarch64 => "runtime.aarch64.geomean",
            Self::X86_64 => "runtime.x86_64.geomean",
        }
    }

    fn binary_size_dimension_id(self) -> &'static str {
        match self {
            Self::Aarch64 => "efficiency.aarch64.binary-size",
            Self::X86_64 => "efficiency.x86_64.binary-size",
        }
    }

    fn clean_compile_dimension_id(self) -> &'static str {
        match self {
            Self::Aarch64 => "compile.aarch64.clean-release",
            Self::X86_64 => "compile.x86_64.clean-release",
        }
    }

    fn incremental_compile_dimension_id(self) -> &'static str {
        match self {
            Self::Aarch64 => "compile.aarch64.incremental-debug",
            Self::X86_64 => "compile.x86_64.incremental-debug",
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Aarch64 => "AArch64/Arm64",
            Self::X86_64 => "x86-64",
        }
    }

    fn evidence_token(self) -> &'static str {
        match self {
            Self::Aarch64 => "aarch64",
            Self::X86_64 => "x86_64",
        }
    }
}

#[derive(Debug, Default)]
struct ArchDetection {
    arch: Option<LaunchArch>,
    ambiguous: bool,
}

impl ArchDetection {
    fn observe(&mut self, value: Option<&str>) {
        let Some(candidate) = value.and_then(arch_from_text) else {
            return;
        };
        match self.arch {
            Some(existing) if existing != candidate => self.ambiguous = true,
            Some(_) => {}
            None => self.arch = Some(candidate),
        }
    }
}

fn arch_from_text(value: &str) -> Option<LaunchArch> {
    let lower = value.to_ascii_lowercase();
    let aarch64 = lower.contains("aarch64") || lower.contains("arm64");
    let x86_64 = lower.contains("x86_64") || lower.contains("x86-64") || lower.contains("amd64");
    match (aarch64, x86_64) {
        (true, false) => Some(LaunchArch::Aarch64),
        (false, true) => Some(LaunchArch::X86_64),
        _ => None,
    }
}

fn compat_target_arch_from_text(value: &str) -> Option<LaunchArch> {
    match value.trim().to_ascii_lowercase().replace('-', "_").as_str() {
        "aarch64" => Some(LaunchArch::Aarch64),
        "x86_64" => Some(LaunchArch::X86_64),
        _ => None,
    }
}

fn compatibility_summary_arch(summary: &CompatibilityResultSummaryInput) -> Option<LaunchArch> {
    summary.target_arch.as_deref().and_then(compat_target_arch_from_text)
}

fn report_arch(report: &Value) -> ArchDetection {
    let mut detection = ArchDetection::default();
    for key in [
        "target_arch",
        "target",
        "target_triple",
        "host_arch",
        "host",
        "host_triple",
        "architecture",
    ] {
        detection.observe(value_at(report, key));
    }
    for container in ["runner", "host", "target", "metadata", "machine", "platform"] {
        if let Some(object) = report.get(container) {
            for key in [
                "arch",
                "architecture",
                "target_arch",
                "target",
                "target_triple",
                "host_arch",
                "host",
                "host_triple",
            ] {
                detection.observe(value_at(object, key));
            }
        }
    }
    detection
}

fn compatibility_aggregate_dimension(
    path: &Path,
    arch: LaunchArch,
    passed: u64,
    failed: u64,
    unknown: u64,
) -> DimensionInput {
    let rows = passed + failed + unknown;
    let status = if rows == 0 || unknown > 0 {
        DeclaredStatus::Unknown
    } else if failed > 0 {
        DeclaredStatus::Fail
    } else {
        DeclaredStatus::Pass
    };
    let ai_hint = match status {
        DeclaredStatus::Pass => format!(
            "Keep the {} upstream-compat summary green for every reviewed commit.",
            arch.label()
        ),
        DeclaredStatus::Fail => format!(
            "Fix {} upstream-compat failures before claiming Rust compatibility.",
            arch.label()
        ),
        DeclaredStatus::Unknown => format!(
            "Rerun the {} upstream-compat gate until every row is classified.",
            arch.label()
        ),
    };
    DimensionInput {
        id: arch.compat_dimension_id().to_string(),
        title: format!("{} Rust toolchain compatibility", arch.label()),
        category: DimensionCategory::Compatibility,
        metric: Some(MetricKind::PassRate),
        comparison_baseline: Some(
            "upstream rustc/rustdoc/cargo/rustfmt/clippy/miri/rust-analyzer on the adopted snapshot"
                .to_string(),
        ),
        required: true,
        rust_value: None,
        trust_value: None,
        higher_is_better: Some(true),
        min_trust_delta_pct: None,
        max_trust_regression_pct: None,
        status: Some(status),
        unit: Some("compatibility_summary".to_string()),
        weight: 1.0,
        evidence: vec![format!(
            "{}: target_arch={} rows={} passed={} failed={} unknown={}",
            path.display(),
            arch.evidence_token(),
            rows,
            passed,
            failed,
            unknown
        )],
        ai_hint: Some(ai_hint),
        owner: None,
        evidence_source: DimensionEvidenceSource::CompatibilitySummaryAggregate,
    }
}

fn upsert_dimension(dimensions: &mut Vec<DimensionInput>, dimension: DimensionInput) {
    if let Some(existing) = dimensions.iter_mut().find(|existing| existing.id == dimension.id) {
        *existing = dimension;
    } else {
        dimensions.push(dimension);
    }
}

fn read_proof_functional_program_index_report(path: &Path) -> Result<DimensionInput> {
    let content = read_bounded_utf8_file(path, MAX_SAVED_PROOF_REPORT_BYTES)
        .with_context(|| format!("failed to read {} safely", path.display()))?;
    let report: Value = serde_json::from_str(&content)
        .with_context(|| format!("failed to parse JSON program-index report {}", path.display()))?;

    if report.get("schema").and_then(Value::as_str) != Some(PROGRAM_INDEX_REPORT_SCHEMA) {
        bail!(
            "program-index report {} has schema {:?}, expected {PROGRAM_INDEX_REPORT_SCHEMA}",
            path.display(),
            report.get("schema").and_then(Value::as_str)
        );
    }

    let results = report
        .get("results")
        .and_then(Value::as_array)
        .with_context(|| format!("program-index report {} has no results array", path.display()))?;
    let declared_total_rows = report
        .get("summary")
        .and_then(|summary| summary.get("total_rows"))
        .and_then(Value::as_u64)
        .with_context(|| {
            format!("program-index report {} has no summary.total_rows", path.display())
        })?;
    if declared_total_rows != results.len() as u64 {
        bail!(
            "program-index report {} declares summary.total_rows={declared_total_rows}, but has {} result rows",
            path.display(),
            results.len()
        );
    }

    let mut blockers = Vec::new();
    if report.get("runner").and_then(|runner| runner.get("python_used")).and_then(Value::as_bool)
        != Some(false)
    {
        blockers.push("report runner must be Rust-owned with runner.python_used=false".to_string());
    }
    if report.get("dry_run").and_then(Value::as_bool) != Some(false) {
        blockers.push("program-index proof evidence must be a non-dry-run report".to_string());
    }
    blockers.extend(program_index_report_provenance_blockers(&report));
    validate_program_index_domination_evidence(&report, &mut blockers);
    validate_proof_design_verifier_evidence(&report, &mut blockers);
    validate_proof_functional_report_summary(&report, &mut blockers);

    let corpus_proof_design = report
        .get("corpus")
        .and_then(|corpus| corpus.get("suites"))
        .and_then(|suites| suites.get(PROOF_FUNCTIONAL_SUITE))
        .and_then(Value::as_u64)
        .unwrap_or(0);
    if corpus_proof_design == 0 {
        blockers.push(format!("corpus.suites.{PROOF_FUNCTIONAL_SUITE} must be greater than zero"));
    }
    if !json_string_array_contains(
        report.get("corpus").and_then(|corpus| corpus.get("slots")),
        PROOF_FUNCTIONAL_SLOT,
    ) {
        blockers.push(format!("corpus.slots must include {PROOF_FUNCTIONAL_SLOT}"));
    }

    let proof_rows = results
        .iter()
        .filter(|row| {
            value_at(row, "suite") == Some(PROOF_FUNCTIONAL_SUITE)
                && value_at(row, "slot") == Some(PROOF_FUNCTIONAL_SLOT)
        })
        .collect::<Vec<_>>();
    validate_frontend_lowering_rows(&report, &proof_rows, &mut blockers);
    let observed = summarize_proof_functional_rows(&proof_rows, corpus_proof_design, &mut blockers);

    let status = if blockers.is_empty() {
        DeclaredStatus::Pass
    } else if observed.rows == 0 || observed.good_rows == 0 || observed.flawed_rows == 0 {
        DeclaredStatus::Unknown
    } else {
        DeclaredStatus::Fail
    };
    let evidence = vec![format!(
        "{}: schema={} proof_design_rows={} good={} flawed={} passed_observations={} obligations={} proved={} flawed_failed_obligations={} unknown={} runtime_checked={} blockers={}",
        path.display(),
        PROGRAM_INDEX_REPORT_SCHEMA,
        observed.rows,
        observed.good_rows,
        observed.flawed_rows,
        observed.passed_observations,
        observed.total_obligations,
        observed.proved_obligations,
        observed.flawed_failed_obligations,
        observed.unknown_obligations,
        observed.runtime_checked_obligations,
        blockers.len()
    )];
    let ai_hint = if blockers.is_empty() {
        "Keep this proof-design program-index report fresh for the reviewed commit.".to_string()
    } else {
        format!(
            "Rerun `{PROOF_FUNCTIONAL_EVIDENCE_COMMAND}` and provide a report with clean proof-design trust-verify observations. Blockers: {}",
            blockers.join("; ")
        )
    };

    Ok(DimensionInput {
        id: PROOF_FUNCTIONAL_DIMENSION_ID.to_string(),
        title: "Functional proof capability beyond Rust plus existing verifier tools".to_string(),
        category: DimensionCategory::Verification,
        metric: Some(MetricKind::Score),
        comparison_baseline: Some(
            "best practical Rust stack using Kani, Creusot, Prusti, Verus, MIRAI, Miri, sanitizers, Z3, and manual specs"
                .to_string(),
        ),
        required: true,
        rust_value: if status == DeclaredStatus::Pass { Some(0.0) } else { None },
        trust_value: if status == DeclaredStatus::Pass {
            Some(observed.passed_observations as f64)
        } else {
            None
        },
        higher_is_better: Some(true),
        min_trust_delta_pct: None,
        max_trust_regression_pct: None,
        status: Some(status),
        unit: Some("proof_design_trust_verify_observation".to_string()),
        weight: 1.0,
        evidence,
        ai_hint: Some(ai_hint),
        owner: None,
        evidence_source: DimensionEvidenceSource::ProgramIndexProofReport,
    })
}

fn read_proof_unsafe_memory_report(path: &Path) -> Result<DimensionInput> {
    let content = read_bounded_utf8_file(path, MAX_SAVED_PROOF_REPORT_BYTES)
        .with_context(|| format!("failed to read {} safely", path.display()))?;
    let report: ProofUnsafeMemoryReportInput =
        serde_json::from_str(&content).with_context(|| {
            format!("failed to parse JSON unsafe-memory proof report {}", path.display())
        })?;

    if report.schema != PROOF_UNSAFE_MEMORY_REPORT_SCHEMA {
        bail!(
            "unsafe-memory proof report {} has schema `{}`, expected `{PROOF_UNSAFE_MEMORY_REPORT_SCHEMA}`",
            path.display(),
            report.schema
        );
    }

    let mut blockers = Vec::new();
    if !is_full_git_sha(&report.candidate_commit) {
        blockers.push(format!(
            "candidate_commit must be a full git SHA, got `{}`",
            report.candidate_commit
        ));
    }
    if report.repo_dirty {
        blockers.push("repo_dirty must be false".to_string());
    }
    validate_proof_unsafe_memory_producer(&report.producer, &mut blockers);
    validate_proof_unsafe_memory_artifact_binding(path, &report, &mut blockers);
    validate_proof_unsafe_memory_coverage(&report.coverage, &mut blockers);
    if !report.unsupported.is_empty() {
        blockers.push(format!(
            "unsupported must be empty, got {} entr{}",
            report.unsupported.len(),
            if report.unsupported.len() == 1 { "y" } else { "ies" }
        ));
    }

    let status = if blockers.is_empty() { DeclaredStatus::Pass } else { DeclaredStatus::Fail };
    let coverage = report.coverage;
    let evidence = vec![format!(
        "{}: schema={} candidate_commit={} proof_report_path={} unsafe_blocks={}/{} unsafe_operations={}/{} memory_obligations={}/{} unsupported={} blockers={}",
        path.display(),
        PROOF_UNSAFE_MEMORY_REPORT_SCHEMA,
        report.candidate_commit,
        report.proof_report_path,
        coverage.unsafe_blocks_proved,
        coverage.unsafe_blocks_total,
        coverage.unsafe_operations_proved,
        coverage.unsafe_operations_total,
        coverage.memory_obligations_proved,
        coverage.memory_obligations_total,
        report.unsupported.len(),
        blockers.len()
    )];
    let ai_hint = if blockers.is_empty() {
        "Keep the unsafe-memory proof report fresh for the reviewed commit.".to_string()
    } else {
        format!(
            "Rerun `{PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND}` and regenerate {PROOF_UNSAFE_MEMORY_REPORT_SCHEMA}. Blockers: {}",
            blockers.join("; ")
        )
    };

    Ok(DimensionInput {
        id: PROOF_UNSAFE_MEMORY_DIMENSION_ID.to_string(),
        title: "Unsafe-code memory proof coverage".to_string(),
        category: DimensionCategory::Safety,
        metric: Some(MetricKind::PassRate),
        comparison_baseline: Some(
            "Rust unsafe review plus Miri/sanitizers/Kani/Creusot-style bounded or annotated checks"
                .to_string(),
        ),
        required: true,
        rust_value: if status == DeclaredStatus::Pass { Some(0.0) } else { None },
        trust_value: if status == DeclaredStatus::Pass {
            Some(coverage.memory_obligations_proved as f64)
        } else {
            None
        },
        higher_is_better: Some(true),
        min_trust_delta_pct: None,
        max_trust_regression_pct: None,
        status: Some(status),
        unit: Some("unsafe_memory_obligation".to_string()),
        weight: 1.0,
        evidence,
        ai_hint: Some(ai_hint),
        owner: None,
        evidence_source: DimensionEvidenceSource::ProofUnsafeMemoryReport,
    })
}

fn validate_proof_unsafe_memory_producer(
    producer: &ProofUnsafeMemoryProducerInput,
    blockers: &mut Vec<String>,
) {
    if !producer.native {
        blockers.push("producer.native must be true".to_string());
    }
    if producer.command.trim() != PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND {
        blockers.push(format!(
            "producer.command must be `{PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND}`, got `{}`",
            producer.command
        ));
    }
    if text_declares_python_command_marker(&producer.command) {
        blockers.push("producer.command must not reference Python tooling".to_string());
    }
}

fn validate_proof_unsafe_memory_artifact_binding(
    report_path: &Path,
    report: &ProofUnsafeMemoryReportInput,
    blockers: &mut Vec<String>,
) {
    let proof_report_path = report.proof_report_path.trim();
    if !evidence_ref_path_is_safe(proof_report_path) {
        blockers
            .push(format!("proof_report_path `{proof_report_path}` must be a safe relative path"));
        return;
    }
    let expected_hash = match normalize_sha256_digest(&report.proof_report_hash) {
        Some(hash) => hash,
        None => {
            blockers.push("proof_report_hash must be a sha256 hex digest".to_string());
            return;
        }
    };
    let proof_report = match resolve_product_proof_evidence_path(
        report_path.parent().unwrap_or_else(|| Path::new(".")),
        proof_report_path,
    ) {
        Ok(path) => path,
        Err(error) => {
            blockers.push(format!(
                "proof_report_path `{proof_report_path}` could not be resolved safely: {error}"
            ));
            return;
        }
    };
    match file_sha256_hex(&proof_report) {
        Ok(actual) if actual == expected_hash => {}
        Ok(actual) => blockers.push(format!(
            "proof_report_hash declares `{expected_hash}`, but {} hashes to `{actual}`",
            proof_report.display()
        )),
        Err(error) => blockers
            .push(format!("could not hash proof_report_path {}: {error}", proof_report.display())),
    }
}

fn validate_proof_unsafe_memory_coverage(
    coverage: &ProofUnsafeMemoryCoverageInput,
    blockers: &mut Vec<String>,
) {
    validate_positive_fully_proved_count(
        "unsafe_blocks",
        coverage.unsafe_blocks_total,
        coverage.unsafe_blocks_proved,
        blockers,
    );
    validate_positive_fully_proved_count(
        "unsafe_operations",
        coverage.unsafe_operations_total,
        coverage.unsafe_operations_proved,
        blockers,
    );
    validate_positive_fully_proved_count(
        "memory_obligations",
        coverage.memory_obligations_total,
        coverage.memory_obligations_proved,
        blockers,
    );
}

fn validate_positive_fully_proved_count(
    label: &str,
    total: u64,
    proved: u64,
    blockers: &mut Vec<String>,
) {
    if total == 0 {
        blockers.push(format!("{label}_total must be positive"));
    }
    if proved != total {
        blockers.push(format!(
            "{label}_proved must equal {label}_total, got proved={proved} total={total}"
        ));
    }
}

fn validate_proof_functional_report_summary(report: &Value, blockers: &mut Vec<String>) {
    let summary = report.get("summary").unwrap_or(&Value::Null);
    for key in ["failed", "excepted", "skipped", "planned", "raw_failed_before_exceptions"] {
        let value = json_u64(summary, key);
        if value != 0 {
            blockers.push(format!("summary.{key} must be 0 for proof evidence, got {value}"));
        }
    }
    for key in ["known_good_pass", "known_flawed_rejection"] {
        let status = summary.get(key).and_then(|value| value.get("status")).and_then(Value::as_str);
        if status != Some("passed") {
            blockers.push(format!("summary.{key}.status must be passed, got {status:?}"));
        }
    }
    validate_frontend_lowering_gate_summary(summary, blockers);
}

fn validate_frontend_lowering_gate_summary(summary: &Value, blockers: &mut Vec<String>) {
    let gate = summary.get("unsupported_frontend_lowering_gate").unwrap_or(&Value::Null);
    if value_at(gate, "schema") != Some(UNSUPPORTED_FRONTEND_LOWERING_GATE_SCHEMA) {
        blockers.push(format!(
            "summary.unsupported_frontend_lowering_gate.schema must be {UNSUPPORTED_FRONTEND_LOWERING_GATE_SCHEMA}, got {:?}",
            value_at(gate, "schema")
        ));
    }
    if value_at(gate, "status") != Some("passed") {
        blockers.push(format!(
            "summary.unsupported_frontend_lowering_gate.status must be passed, got {:?}",
            value_at(gate, "status")
        ));
    }
    if gate
        .get("observation_scope")
        .and_then(|scope| scope.get("completeness_claim"))
        .and_then(Value::as_bool)
        != Some(true)
    {
        blockers.push(
            "summary.unsupported_frontend_lowering_gate must make an authenticated typed-ingress completeness claim"
                .to_string(),
        );
    }
    let observation_scope = gate.get("observation_scope").unwrap_or(&Value::Null);
    if value_at(observation_scope, "completeness_claim_scope")
        != Some("typed_trust_ir_verifier_ingress_only")
    {
        blockers.push(
            "summary.unsupported_frontend_lowering_gate completeness must be scoped to typed TrustIr verifier ingress"
                .to_string(),
        );
    }
    let transition = gate.get("frontend_transition").unwrap_or(&Value::Null);
    if transition.get("direct_frontend_proof_authority").and_then(Value::as_bool) != Some(false)
        || transition.get("producer_authenticated_by_transport").and_then(Value::as_bool)
            != Some(false)
        || transition.get("mir_compatibility_proof_path_retained").and_then(Value::as_bool)
            != Some(true)
    {
        blockers.push(
            "frontend lowering gate must remain producer-neutral, deny unwired direct-frontend proof authority, and retain temporary authenticated MIR-derived compatibility coverage"
                .to_string(),
        );
    }
    let compatibility = gate.get("backward_compatibility").unwrap_or(&Value::Null);
    if compatibility.get("legacy_gate_preserved").and_then(Value::as_bool) != Some(true)
        || value_at(compatibility, "legacy_summary_field") != Some("unsupported_mir_gate")
        || value_at(compatibility, "legacy_schema") != Some(UNSUPPORTED_MIR_GATE_SCHEMA)
    {
        blockers.push(
            "summary.unsupported_frontend_lowering_gate must preserve the legacy unsupported_mir_gate contract"
                .to_string(),
        );
    }

    let native = gate.get("native_evidence").unwrap_or(&Value::Null);
    let obligations = json_u64(native, "obligation_results");
    let typed = json_u64(native, "typed_transport_results");
    let malformed = json_u64(native, "malformed_typed_transport_results");
    let native_ir = json_u64(native, "native_trust_ir_results");
    let proved = json_u64(native, "proved_results");
    let publishable = json_u64(native, "publishable_native_proof_results");
    if obligations == 0 {
        blockers.push(
            "summary.unsupported_frontend_lowering_gate.native_evidence.obligation_results must be positive"
                .to_string(),
        );
    }
    if typed != obligations || native_ir != obligations || malformed != 0 {
        blockers.push(format!(
            "frontend lowering native evidence must cover every typed obligation (obligations={obligations}, typed={typed}, native_trust_ir={native_ir}, malformed={malformed})"
        ));
    }
    if publishable != proved {
        blockers.push(format!(
            "frontend lowering publication-grade native proofs must cover every proved obligation (proved={proved}, publishable={publishable})"
        ));
    }

    let legacy = summary.get("unsupported_mir_gate").unwrap_or(&Value::Null);
    if value_at(legacy, "schema") != Some(UNSUPPORTED_MIR_GATE_SCHEMA)
        || value_at(legacy, "status") != Some("passed")
    {
        blockers.push(
            "summary.unsupported_mir_gate must remain present and passed under its legacy schema"
                .to_string(),
        );
    }
}

fn validate_frontend_lowering_rows(report: &Value, rows: &[&Value], blockers: &mut Vec<String>) {
    let keys = [
        "obligation_results",
        "typed_transport_results",
        "malformed_typed_transport_results",
        "native_trust_ir_results",
        "proved_results",
        "publishable_native_proof_results",
    ];
    let mut sums = BTreeMap::new();
    for key in keys {
        sums.insert(key, 0_u64);
    }
    for row in rows {
        let program = value_at(row, "program_id").unwrap_or("<missing-program>");
        if value_at(row, "unsupported_frontend_lowering_gate_status")
            != Some("native_evidence_complete")
        {
            blockers.push(format!(
                "{program}: unsupported_frontend_lowering_gate_status must be native_evidence_complete"
            ));
        }
        let transport = row.get("transport").unwrap_or(&Value::Null);
        let total = json_u64(transport, "obligation_results");
        let typed = json_u64(transport, "typed_transport_results");
        let malformed = json_u64(transport, "malformed_typed_transport_results");
        let native = json_u64(transport, "native_trust_ir_results");
        let proved = json_u64(transport, "proved_results");
        let publishable = json_u64(transport, "publishable_native_proof_results");
        if total == 0 || typed != total || native != total || malformed != 0 {
            blockers.push(format!(
                "{program}: typed TrustIr verifier-ingress evidence must cover every obligation (obligations={total}, typed={typed}, native_trust_ir={native}, malformed={malformed})"
            ));
        }
        if publishable != proved {
            blockers.push(format!(
                "{program}: publication-grade native proofs must cover every proved obligation (proved={proved}, publishable={publishable})"
            ));
        }
        for key in keys {
            let value = json_u64(transport, key);
            let sum = sums.get_mut(key).expect("frontend summary key initialized");
            *sum = sum.saturating_add(value);
        }
    }

    let summary_native = report
        .get("summary")
        .and_then(|summary| summary.get("unsupported_frontend_lowering_gate"))
        .and_then(|gate| gate.get("native_evidence"))
        .unwrap_or(&Value::Null);
    for key in keys {
        let declared = json_u64(summary_native, key);
        let observed = sums[key];
        if declared != observed {
            blockers.push(format!(
                "summary.unsupported_frontend_lowering_gate.native_evidence.{key}={declared} must match proof-design rows={observed}"
            ));
        }
    }
}

fn validate_program_index_domination_evidence(report: &Value, blockers: &mut Vec<String>) {
    let evidence = report.get("program_index_evidence").unwrap_or(&Value::Null);
    if !evidence.is_object() {
        blockers.push(
            "program_index_evidence must be present for domination proof evidence".to_string(),
        );
        return;
    }

    if value_at(evidence, "status") != Some("admissible") {
        blockers.push(format!(
            "program_index_evidence.status must be admissible, got {:?}",
            value_at(evidence, "status")
        ));
    }
    if evidence.get("admissible_for_domination").and_then(Value::as_bool) != Some(true) {
        blockers.push("program_index_evidence.admissible_for_domination must be true".to_string());
    }
    if json_u64(evidence, "selected_candidate_rows") != 0 {
        blockers.push(format!(
            "program_index_evidence.selected_candidate_rows must be 0, got {}",
            json_u64(evidence, "selected_candidate_rows")
        ));
    }
    if json_u64(evidence, "selected_gating_rows") == 0 {
        blockers.push("program_index_evidence.selected_gating_rows must be positive".to_string());
    }
    if json_u64(evidence, "selected_admissible_gating_rows") == 0 {
        blockers.push(
            "program_index_evidence.selected_admissible_gating_rows must be positive".to_string(),
        );
    }

    let proof_design_count = evidence
        .get("selected_suite_counts")
        .and_then(|counts| counts.get(PROOF_FUNCTIONAL_SUITE))
        .and_then(Value::as_u64)
        .unwrap_or(0);
    if proof_design_count == 0 {
        blockers.push(format!(
            "program_index_evidence.selected_suite_counts.{PROOF_FUNCTIONAL_SUITE} must be positive"
        ));
    }

    let proof_design = evidence
        .get("selected_suites")
        .and_then(|suites| suites.get(PROOF_FUNCTIONAL_SUITE))
        .unwrap_or(&Value::Null);
    if proof_design.get("admissible_for_domination").and_then(Value::as_bool) != Some(true) {
        blockers.push(format!(
            "program_index_evidence.selected_suites.{PROOF_FUNCTIONAL_SUITE}.admissible_for_domination must be true"
        ));
    }
    if proof_design.get("candidate_evidence").and_then(Value::as_bool) != Some(false) {
        blockers.push(format!(
            "program_index_evidence.selected_suites.{PROOF_FUNCTIONAL_SUITE}.candidate_evidence must be false"
        ));
    }
    if json_u64(proof_design, "candidate_rows") != 0 {
        blockers.push(format!(
            "program_index_evidence.selected_suites.{PROOF_FUNCTIONAL_SUITE}.candidate_rows must be 0, got {}",
            json_u64(proof_design, "candidate_rows")
        ));
    }
}

fn validate_proof_design_verifier_evidence(report: &Value, blockers: &mut Vec<String>) {
    let evidence = report.get("proof_design_verifier_evidence").unwrap_or(&Value::Null);
    if !evidence.is_object() {
        blockers.push(
            "proof_design_verifier_evidence must be present for domination proof evidence"
                .to_string(),
        );
        return;
    }
    if value_at(evidence, "schema") != Some(PROOF_DESIGN_VERIFIER_EVIDENCE_SCHEMA) {
        blockers.push(format!(
            "proof_design_verifier_evidence.schema must be {PROOF_DESIGN_VERIFIER_EVIDENCE_SCHEMA}, got {:?}",
            value_at(evidence, "schema")
        ));
    }
    if value_at(evidence, "status") != Some("passed") {
        blockers.push(format!(
            "proof_design_verifier_evidence.status must be passed, got {:?}",
            value_at(evidence, "status")
        ));
    }
    if evidence.get("required").and_then(Value::as_bool) != Some(true) {
        blockers.push("proof_design_verifier_evidence.required must be true".to_string());
    }
    if evidence.get("admissible_for_domination").and_then(Value::as_bool) != Some(true) {
        blockers.push(
            "proof_design_verifier_evidence.admissible_for_domination must be true".to_string(),
        );
    }
    let selected_programs = json_u64(evidence, "selected_programs");
    let verifier_rows = json_u64(evidence, "verifier_rows");
    let accepted_rows = json_u64(evidence, "accepted_rows");
    if selected_programs == 0 {
        blockers.push("proof_design_verifier_evidence.selected_programs must be positive".into());
    }
    if verifier_rows != selected_programs {
        blockers.push(format!(
            "proof_design_verifier_evidence.verifier_rows={verifier_rows} must match selected_programs={selected_programs}"
        ));
    }
    if accepted_rows != verifier_rows {
        blockers.push(format!(
            "proof_design_verifier_evidence.accepted_rows={accepted_rows} must match verifier_rows={verifier_rows}"
        ));
    }
    if value_at(evidence, "transport_protocol") != Some("stderr-line-prefix") {
        blockers.push(
            "proof_design_verifier_evidence.transport_protocol must be stderr-line-prefix"
                .to_string(),
        );
    }
    if value_at(evidence, "transport_prefix") != Some("TRUST_JSON:") {
        blockers.push("proof_design_verifier_evidence.transport_prefix must be TRUST_JSON:".into());
    }
    if evidence
        .get("transport_sources")
        .and_then(Value::as_array)
        .is_none_or(|sources| sources.is_empty())
    {
        blockers.push("proof_design_verifier_evidence.transport_sources must be nonempty".into());
    }

    let stage2 = evidence.get("stage2_binding").unwrap_or(&Value::Null);
    if value_at(stage2, "status") != Some("bound") {
        blockers.push(format!(
            "proof_design_verifier_evidence.stage2_binding.status must be bound, got {:?}",
            value_at(stage2, "status")
        ));
    }
    if stage2.get("repo_stage2").and_then(Value::as_bool) != Some(true) {
        blockers
            .push("proof_design_verifier_evidence.stage2_binding.repo_stage2 must be true".into());
    }
    if stage2.get("canonical_entrypoint").and_then(Value::as_bool) != Some(true) {
        blockers.push(
            "proof_design_verifier_evidence.stage2_binding.canonical_entrypoint must be true"
                .into(),
        );
    }
    if value_at(stage2, "canonical_binary") != Some("trustc") {
        blockers.push(
            "proof_design_verifier_evidence.stage2_binding.canonical_binary must be trustc".into(),
        );
    }
    if stage2.get("stage2_roots").and_then(Value::as_array).is_none_or(|roots| roots.is_empty()) {
        blockers.push(
            "proof_design_verifier_evidence.stage2_binding.stage2_roots must be nonempty".into(),
        );
    }

    let rows = evidence.get("rows").and_then(Value::as_array).cloned().unwrap_or_default();
    if rows.len() as u64 != verifier_rows {
        blockers.push(format!(
            "proof_design_verifier_evidence.rows length={} must match verifier_rows={verifier_rows}",
            rows.len()
        ));
    }
    for row in rows {
        let program = value_at(&row, "program_id").unwrap_or("<unknown>");
        if row.get("accepted").and_then(Value::as_bool) != Some(true) {
            blockers
                .push(format!("{program}: proof_design_verifier_evidence row must be accepted"));
        }
        let source = row.get("transport_source").unwrap_or(&Value::Null);
        if value_at(source, "protocol") != Some("stderr-line-prefix") {
            blockers.push(format!(
                "{program}: proof_design_verifier_evidence transport_source.protocol must be stderr-line-prefix"
            ));
        }
        if value_at(source, "prefix") != Some("TRUST_JSON:") {
            blockers.push(format!(
                "{program}: proof_design_verifier_evidence transport_source.prefix must be TRUST_JSON:"
            ));
        }
        if value_at(source, "stderr_path").is_none_or(str::is_empty) {
            blockers.push(format!(
                "{program}: proof_design_verifier_evidence transport_source.stderr_path must be present"
            ));
        }
        let transport = row.get("transport").unwrap_or(&Value::Null);
        if json_u64(transport, "function_results") == 0 {
            blockers.push(format!(
                "{program}: proof_design_verifier_evidence transport.function_results must be positive"
            ));
        }
        if json_u64(transport, "malformed_lines") != 0 {
            blockers.push(format!(
                "{program}: proof_design_verifier_evidence transport.malformed_lines must be 0"
            ));
        }
        let total = json_u64(transport, "total");
        if total == 0 {
            blockers.push(format!(
                "{program}: proof_design_verifier_evidence transport.total must be positive"
            ));
        }
        for (primary, corroborating) in [
            ("total", "obligation_results"),
            ("proved", "proved_results"),
            ("failed", "failed_results"),
            ("unknown", "unknown_results"),
            ("runtime_checked", "runtime_checked_results"),
        ] {
            let primary_value = json_u64(transport, primary);
            let corroborating_value = json_u64(transport, corroborating);
            if primary_value != corroborating_value {
                blockers.push(format!(
                    "{program}: proof_design_verifier_evidence transport.{primary}={primary_value} must match {corroborating}={corroborating_value}"
                ));
            }
        }
        let obligation_results = json_u64(transport, "obligation_results");
        let typed = json_u64(transport, "typed_transport_results");
        let malformed_typed = json_u64(transport, "malformed_typed_transport_results");
        let native = json_u64(transport, "native_trust_ir_results");
        let proved = json_u64(transport, "proved_results");
        let publishable = json_u64(transport, "publishable_native_proof_results");
        if typed != obligation_results || native != obligation_results || malformed_typed != 0 {
            blockers.push(format!(
                "{program}: proof_design_verifier_evidence typed TrustIr verifier-ingress evidence must cover every obligation (obligations={obligation_results}, typed={typed}, native_trust_ir={native}, malformed={malformed_typed})"
            ));
        }
        if publishable != proved {
            blockers.push(format!(
                "{program}: proof_design_verifier_evidence publication-grade native proofs must cover every proved obligation (proved={proved}, publishable={publishable})"
            ));
        }
    }
}

#[derive(Debug, Default)]
struct ProofFunctionalObservationSummary {
    rows: u64,
    good_rows: u64,
    flawed_rows: u64,
    passed_observations: u64,
    total_obligations: u64,
    proved_obligations: u64,
    flawed_failed_obligations: u64,
    unknown_obligations: u64,
    runtime_checked_obligations: u64,
}

fn summarize_proof_functional_rows(
    proof_rows: &[&Value],
    corpus_proof_design: u64,
    blockers: &mut Vec<String>,
) -> ProofFunctionalObservationSummary {
    let mut observed =
        ProofFunctionalObservationSummary { rows: proof_rows.len() as u64, ..Default::default() };
    if proof_rows.is_empty() {
        blockers.push("no proof-design trust-verify rows were present".to_string());
        return observed;
    }
    if corpus_proof_design != 0 && corpus_proof_design != observed.rows {
        blockers.push(format!(
            "corpus.suites.{PROOF_FUNCTIONAL_SUITE}={corpus_proof_design} but results contain {} {PROOF_FUNCTIONAL_SUITE} {PROOF_FUNCTIONAL_SLOT} rows",
            observed.rows
        ));
    }

    for row in proof_rows {
        let program = value_at(row, "program_id").unwrap_or("<unknown>");
        let variant = value_at(row, "variant").unwrap_or("<unknown>");
        let expected = match variant {
            "good" => {
                observed.good_rows += 1;
                "verify_pass"
            }
            "flawed" => {
                observed.flawed_rows += 1;
                "verify_fail"
            }
            other => {
                blockers.push(format!("{program}: unexpected proof-design variant `{other}`"));
                continue;
            }
        };
        let row_expected = value_at(row, "expected");
        let row_observed = value_at(row, "observed");
        let row_outcome = value_at(row, "outcome");
        let classification = value_at(row, "classification");
        if row_expected != Some(expected) || row_observed != Some(expected) {
            blockers.push(format!(
                "{program}: expected/observed must both be {expected}, got expected={row_expected:?} observed={row_observed:?}"
            ));
        }
        if row_outcome != Some("passed") {
            blockers.push(format!("{program}: outcome must be passed, got {row_outcome:?}"));
        }
        if classification != Some("as-expected") {
            blockers.push(format!(
                "{program}: classification must be as-expected, got {classification:?}"
            ));
        }
        if row.get("obligations").and_then(Value::as_array).is_none_or(|items| items.is_empty()) {
            blockers.push(format!("{program}: obligations array must be nonempty"));
        }

        let transport = row.get("transport").unwrap_or(&Value::Null);
        let total = corroborated_transport_counter(
            transport,
            program,
            "total",
            "obligation_results",
            blockers,
        );
        let proved = corroborated_transport_counter(
            transport,
            program,
            "proved",
            "proved_results",
            blockers,
        );
        let failed = corroborated_transport_counter(
            transport,
            program,
            "failed",
            "failed_results",
            blockers,
        );
        let unknown = corroborated_transport_counter(
            transport,
            program,
            "unknown",
            "unknown_results",
            blockers,
        );
        let runtime_checked = corroborated_transport_counter(
            transport,
            program,
            "runtime_checked",
            "runtime_checked_results",
            blockers,
        );
        let timed_out =
            json_u64(transport, "timed_out").max(json_u64(transport, "timeout_results"));
        let skipped = json_u64(transport, "skipped").max(json_u64(transport, "skipped_results"));
        observed.total_obligations += total;
        observed.proved_obligations += proved;
        observed.unknown_obligations += unknown + timed_out + skipped;
        observed.runtime_checked_obligations += runtime_checked;

        if total == 0 {
            blockers.push(format!("{program}: transport must report at least one obligation"));
        }
        if unknown > 0 || runtime_checked > 0 || timed_out > 0 || skipped > 0 {
            blockers.push(format!(
                "{program}: transport must have unknown=0, runtime_checked=0, timed_out=0, skipped=0, got unknown={unknown} runtime_checked={runtime_checked} timed_out={timed_out} skipped={skipped}"
            ));
        }
        if proved + failed + unknown + runtime_checked + timed_out + skipped > total {
            blockers.push(format!(
                "{program}: transport counters exceed total={total}, got proved={proved} failed={failed} unknown={unknown} runtime_checked={runtime_checked} timed_out={timed_out} skipped={skipped}"
            ));
        }
        match variant {
            "good" if proved != total || failed > 0 => blockers.push(format!(
                "{program}: good proof row must prove all obligations and have failed=0, got total={total} proved={proved} failed={failed}"
            )),
            "flawed" if failed == 0 => blockers.push(format!(
                "{program}: flawed proof row must carry failed-obligation evidence"
            )),
            "flawed" => observed.flawed_failed_obligations += failed,
            _ => {}
        }
        if row_expected == Some(expected)
            && row_observed == Some(expected)
            && row_outcome == Some("passed")
            && classification == Some("as-expected")
            && total > 0
            && (variant != "good" || proved == total)
            && unknown == 0
            && runtime_checked == 0
            && timed_out == 0
            && skipped == 0
        {
            observed.passed_observations += 1;
        }
    }

    if observed.good_rows == 0 {
        blockers
            .push("proof-design trust-verify evidence must include known-good rows".to_string());
    }
    if observed.flawed_rows == 0 {
        blockers
            .push("proof-design trust-verify evidence must include known-flawed rows".to_string());
    }
    observed
}

fn corroborated_transport_counter(
    transport: &Value,
    program: &str,
    primary_key: &str,
    results_key: &str,
    blockers: &mut Vec<String>,
) -> u64 {
    let primary = transport.get(primary_key).and_then(Value::as_u64);
    let results = transport.get(results_key).and_then(Value::as_u64);
    match (primary, results) {
        (Some(primary), Some(results)) if primary == results => primary,
        (Some(primary), Some(results)) => {
            blockers.push(format!(
                "{program}: transport.{primary_key}={primary} must match transport.{results_key}={results}"
            ));
            primary.max(results)
        }
        (Some(primary), None) => {
            blockers.push(format!(
                "{program}: transport.{results_key} is required to corroborate transport.{primary_key}={primary}"
            ));
            primary
        }
        (None, Some(results)) => {
            blockers.push(format!(
                "{program}: transport.{primary_key} is required to corroborate transport.{results_key}={results}"
            ));
            results
        }
        (None, None) => {
            blockers.push(format!(
                "{program}: transport.{primary_key} and transport.{results_key} are both missing"
            ));
            0
        }
    }
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofConcurrencyReportInput {
    schema: String,
    proof_authority: String,
    proof_pass: bool,
    generated_at: String,
    repo_head: String,
    repo_dirty: bool,
    repo_dirty_metadata: ProofConcurrencyDirtyMetadataInput,
    runner: ProofConcurrencyRunnerInput,
    validation: ProofConcurrencyValidationInput,
    summary: ProofConcurrencySummaryInput,
    obligations: Vec<ProofConcurrencyObligationInput>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofConcurrencyRunnerInput {
    implementation: String,
    language: String,
    runtime: String,
    entrypoint: String,
    command: String,
    argv: Vec<String>,
    tool: String,
    version: String,
    python_used: bool,
    mode: String,
    proof_success_kind: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofConcurrencyValidationInput {
    status: String,
    validator: String,
    validator_sha256: String,
    validation_record_sha256: String,
    authenticated: bool,
    artifacts_authenticated: bool,
    certificates_checked: bool,
    transcripts_replayed: bool,
    dispatches_authenticated: bool,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofConcurrencyDirtyMetadataInput {
    available: bool,
    dirty: bool,
    porcelain_v1: Vec<String>,
    untracked_files: String,
    ignore_submodules: String,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofConcurrencySummaryInput {
    total_obligations: u64,
    proved: u64,
    failed: u64,
    unknown: u64,
    skipped: u64,
    unsupported: u64,
    runtime_checked: u64,
    timed_out: u64,
    manual_pass: u64,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofConcurrencyObligationInput {
    id: String,
    kind: ProofConcurrencyObligationKind,
    status: ProofConcurrencyObligationStatus,
    source: String,
    source_sha256: String,
    memory_model: String,
    proof: ProofConcurrencyProofInput,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofConcurrencyProofInput {
    solver: String,
    certificate_sha256: String,
    transcript_sha256: String,
    dispatch_sha256: String,
    validation_record_sha256: String,
    certificate_checked: bool,
    transcript_replayed: bool,
    dispatch_authenticated: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
enum ProofConcurrencyObligationKind {
    DataRaceFree,
    AtomicOrdering,
    HappensBefore,
}

impl ProofConcurrencyObligationKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::DataRaceFree => "data_race_free",
            Self::AtomicOrdering => "atomic_ordering",
            Self::HappensBefore => "happens_before",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
enum ProofConcurrencyObligationStatus {
    Proved,
    Failed,
    Unknown,
    Skipped,
    Unsupported,
    RuntimeChecked,
    TimedOut,
    ManualPass,
}

impl ProofConcurrencyObligationStatus {
    fn label(self) -> &'static str {
        match self {
            Self::Proved => "proved",
            Self::Failed => "failed",
            Self::Unknown => "unknown",
            Self::Skipped => "skipped",
            Self::Unsupported => "unsupported",
            Self::RuntimeChecked => "runtime_checked",
            Self::TimedOut => "timed_out",
            Self::ManualPass => "manual_pass",
        }
    }
}

fn read_proof_concurrency_report(path: &Path) -> Result<DimensionInput> {
    let content = read_bounded_utf8_file(path, MAX_RELEASE_METADATA_BYTES)
        .with_context(|| format!("failed to read {} safely", path.display()))?;
    let envelope: Value = serde_json::from_str(&content).with_context(|| {
        format!("failed to parse JSON proof-concurrency envelope {}", path.display())
    })?;
    let observed_schema = envelope.get("schema").and_then(Value::as_str).unwrap_or("<missing>");
    if matches!(
        observed_schema,
        "trust.proof-concurrency.report.v1"
            | "trust.proof-concurrency.artifact-audit.v1"
            | "trust.proof-concurrency.demo-audit.v1"
    ) {
        bail!(
            "proof-concurrency report {} uses non-admissible schema `{}`; legacy presence-only, artifact-audit, and demo/stub reports have no proof authority and cannot satisfy `{}`",
            path.display(),
            observed_schema,
            PROOF_CONCURRENCY_REPORT_SCHEMA
        );
    }
    let report: ProofConcurrencyReportInput =
        serde_json::from_str(&content).with_context(|| {
            format!(
                "failed to parse JSON proof-concurrency report {} with schema {}",
                path.display(),
                PROOF_CONCURRENCY_REPORT_SCHEMA
            )
        })?;

    if report.schema != PROOF_CONCURRENCY_REPORT_SCHEMA {
        bail!(
            "proof-concurrency report {} has schema `{}`, expected `{}`",
            path.display(),
            report.schema,
            PROOF_CONCURRENCY_REPORT_SCHEMA
        );
    }

    let mut blockers = Vec::new();
    validate_proof_concurrency_provenance(path, &report, &mut blockers);
    validate_proof_concurrency_authority(&report, &mut blockers);
    validate_proof_concurrency_runner(&report.runner, &mut blockers);
    validate_proof_concurrency_validation(&report.validation, &mut blockers);
    // There is currently no implementation whose identity can be anchored and
    // independently invoked here.  JSON declarations cannot bootstrap their
    // own authority, even if every boolean below is set to true.
    blockers.push(
        "no Trust-owned authenticated concurrency validator/replayer is implemented; JSON declarations, artifact presence, and hashes cannot establish proof authority"
            .to_string(),
    );
    if report.generated_at.trim().is_empty() {
        blockers.push("proof-concurrency report generated_at must be nonempty".to_string());
    }

    let observed = summarize_proof_concurrency_obligations(&report.obligations, &mut blockers);
    validate_proof_concurrency_summary(&report.summary, &observed, &mut blockers);
    for required in PROOF_CONCURRENCY_REQUIRED_OBLIGATION_KINDS {
        if !report.obligations.iter().any(|obligation| obligation.kind.as_str() == required) {
            blockers.push(format!(
                "proof-concurrency report must include a proved {required} obligation"
            ));
        }
    }

    let status = if blockers.is_empty() {
        DeclaredStatus::Pass
    } else if report.obligations.is_empty() {
        DeclaredStatus::Unknown
    } else {
        DeclaredStatus::Fail
    };
    let evidence = vec![format!(
        "{}: schema={} obligations={} proved={} failed={} unknown={} skipped={} unsupported={} runtime_checked={} timed_out={} manual_pass={} blockers={}",
        path.display(),
        PROOF_CONCURRENCY_REPORT_SCHEMA,
        observed.total_obligations,
        observed.proved,
        observed.failed,
        observed.unknown,
        observed.skipped,
        observed.unsupported,
        observed.runtime_checked,
        observed.timed_out,
        observed.manual_pass,
        blockers.len()
    )];
    let ai_hint = if blockers.is_empty() {
        "Keep the proof-concurrency report fresh for the reviewed commit.".to_string()
    } else {
        format!(
            "Rerun `{PROOF_CONCURRENCY_EVIDENCE_COMMAND}` and pass its JSON report with {PROOF_CONCURRENCY_REPORT_FLAG}. Blockers: {}",
            blockers.join("; ")
        )
    };

    Ok(DimensionInput {
        id: PROOF_CONCURRENCY_DIMENSION_ID.to_string(),
        title: "Concurrency, atomics, and data-race proof coverage".to_string(),
        category: DimensionCategory::Safety,
        metric: Some(MetricKind::PassRate),
        comparison_baseline: Some(
            "Rust Send/Sync type checks plus Loom/Miri/sanitizers/manual model checking"
                .to_string(),
        ),
        required: true,
        rust_value: if status == DeclaredStatus::Pass { Some(0.0) } else { None },
        trust_value: if status == DeclaredStatus::Pass { Some(1.0) } else { None },
        higher_is_better: Some(true),
        min_trust_delta_pct: None,
        max_trust_regression_pct: None,
        status: Some(status),
        unit: Some("proof_concurrency_report".to_string()),
        weight: 1.0,
        evidence,
        ai_hint: Some(ai_hint),
        owner: None,
        evidence_source: DimensionEvidenceSource::ProofConcurrencyReport,
    })
}

fn validate_proof_concurrency_provenance(
    path: &Path,
    report: &ProofConcurrencyReportInput,
    blockers: &mut Vec<String>,
) {
    if !is_full_git_sha(&report.repo_head) {
        blockers.push(format!(
            "proof-concurrency report {} repo_head must be a full git SHA, got `{}`",
            path.display(),
            report.repo_head
        ));
    }
    if report.repo_dirty {
        blockers.push(
            "proof-concurrency report repo_dirty must be false for proof evidence".to_string(),
        );
    }
    let metadata = &report.repo_dirty_metadata;
    if !metadata.available {
        blockers.push(
            "proof-concurrency report repo_dirty_metadata.available must be true".to_string(),
        );
    }
    if metadata.dirty {
        blockers
            .push("proof-concurrency report repo_dirty_metadata.dirty must be false".to_string());
    }
    if !metadata.porcelain_v1.is_empty() {
        blockers.push(
            "proof-concurrency report repo_dirty_metadata.porcelain_v1 must be empty".to_string(),
        );
    }
    if metadata.untracked_files != "all" {
        blockers.push(
            "proof-concurrency report repo_dirty_metadata.untracked_files must be all".to_string(),
        );
    }
    if metadata.ignore_submodules != "none" {
        blockers.push(
            "proof-concurrency report repo_dirty_metadata.ignore_submodules must be none"
                .to_string(),
        );
    }
}

fn validate_proof_concurrency_authority(
    report: &ProofConcurrencyReportInput,
    blockers: &mut Vec<String>,
) {
    if report.proof_authority != "trust_kernel_authenticated_replay" {
        blockers.push(format!(
            "proof-concurrency proof_authority must be trust_kernel_authenticated_replay, got `{}`",
            report.proof_authority
        ));
    }
    if !report.proof_pass {
        blockers.push("proof-concurrency proof_pass must be true".to_string());
    }
}

fn validate_proof_concurrency_runner(
    runner: &ProofConcurrencyRunnerInput,
    blockers: &mut Vec<String>,
) {
    for (field, value, expected) in [
        ("implementation", runner.implementation.as_str(), "rust"),
        ("language", runner.language.as_str(), "rust"),
        ("runtime", runner.runtime.as_str(), "native"),
        ("entrypoint", runner.entrypoint.as_str(), "trust-concurrency-validator"),
        ("mode", runner.mode.as_str(), "authenticated_validation_replay"),
        (
            "proof_success_kind",
            runner.proof_success_kind.as_str(),
            "independently_authenticated_certificate_validation_and_replay",
        ),
    ] {
        if value != expected {
            blockers.push(format!(
                "proof-concurrency runner.{field} must be `{expected}`, got `{value}`"
            ));
        }
    }
    if runner.python_used {
        blockers.push("proof-concurrency runner.python_used must be false".to_string());
    }
    for (field, value) in [
        ("command", runner.command.as_str()),
        ("tool", runner.tool.as_str()),
        ("version", runner.version.as_str()),
    ] {
        if !safe_proof_concurrency_label(value) {
            blockers.push(format!(
                "proof-concurrency runner.{field} must be nonempty, bounded, and control-free"
            ));
        }
    }
    if runner.argv.is_empty()
        || runner.argv.iter().any(|value| !safe_proof_concurrency_label(value))
    {
        blockers.push(
            "proof-concurrency runner.argv must contain bounded control-free arguments".to_string(),
        );
    }
}

fn validate_proof_concurrency_validation(
    validation: &ProofConcurrencyValidationInput,
    blockers: &mut Vec<String>,
) {
    if validation.status != "validated" {
        blockers.push(format!(
            "proof-concurrency validation.status must be validated, got `{}`",
            validation.status
        ));
    }
    if !safe_proof_concurrency_validator_identity(&validation.validator) {
        blockers.push(
            "proof-concurrency validation.validator must be a concrete non-stub local validator identity"
                .to_string(),
        );
    }
    for (field, value) in [
        ("validator_sha256", validation.validator_sha256.as_str()),
        ("validation_record_sha256", validation.validation_record_sha256.as_str()),
    ] {
        if !trust_types::digest::is_stable_sha256_hex(value.trim()) {
            blockers.push(format!(
                "proof-concurrency validation.{field} must be a canonical SHA-256 hash"
            ));
        }
    }
    for (field, value) in [
        ("authenticated", validation.authenticated),
        ("artifacts_authenticated", validation.artifacts_authenticated),
        ("certificates_checked", validation.certificates_checked),
        ("transcripts_replayed", validation.transcripts_replayed),
        ("dispatches_authenticated", validation.dispatches_authenticated),
    ] {
        if !value {
            blockers.push(format!("proof-concurrency validation.{field} must be true"));
        }
    }
}

fn safe_proof_concurrency_label(value: &str) -> bool {
    !value.is_empty() && value.len() <= 4096 && !value.chars().any(char::is_control)
}

fn safe_proof_concurrency_validator_identity(value: &str) -> bool {
    let lowered = value.trim().to_ascii_lowercase();
    safe_proof_concurrency_label(value.trim())
        && !lowered.contains("://")
        && !lowered.starts_with("urn:")
        && !["stub", "demo", "fixture", "mock", "manual", "unknown"]
            .iter()
            .any(|marker| lowered.contains(marker))
}

fn summarize_proof_concurrency_obligations(
    obligations: &[ProofConcurrencyObligationInput],
    blockers: &mut Vec<String>,
) -> ProofConcurrencySummaryInput {
    let mut observed = ProofConcurrencySummaryInput {
        total_obligations: obligations.len() as u64,
        ..Default::default()
    };
    if obligations.is_empty() {
        blockers.push("proof-concurrency report obligations array must be nonempty".to_string());
        return observed;
    }

    let mut ids = BTreeSet::new();
    for obligation in obligations {
        let id = obligation_label(&obligation.id);
        if obligation.id.trim().is_empty() {
            blockers.push("proof-concurrency obligation id must be nonempty".to_string());
        } else if !ids.insert(obligation.id.trim().to_string()) {
            blockers.push(format!("proof-concurrency obligation id `{id}` is duplicated"));
        }
        if !canonical_proof_concurrency_source(&obligation.source) {
            blockers.push(format!(
                "{id}: source must be a canonical repository-relative path, not a URI or stub label"
            ));
        }
        if !trust_types::digest::is_stable_sha256_hex(obligation.source_sha256.trim()) {
            blockers.push(format!("{id}: source_sha256 must be a canonical SHA-256 hash"));
        }
        if obligation.memory_model.trim().is_empty() {
            blockers.push(format!("{id}: memory_model must be nonempty"));
        }
        match obligation.status {
            ProofConcurrencyObligationStatus::Proved => observed.proved += 1,
            ProofConcurrencyObligationStatus::Failed => observed.failed += 1,
            ProofConcurrencyObligationStatus::Unknown => observed.unknown += 1,
            ProofConcurrencyObligationStatus::Skipped => observed.skipped += 1,
            ProofConcurrencyObligationStatus::Unsupported => observed.unsupported += 1,
            ProofConcurrencyObligationStatus::RuntimeChecked => observed.runtime_checked += 1,
            ProofConcurrencyObligationStatus::TimedOut => observed.timed_out += 1,
            ProofConcurrencyObligationStatus::ManualPass => observed.manual_pass += 1,
        }
        if obligation.status != ProofConcurrencyObligationStatus::Proved {
            blockers
                .push(format!("{id}: status must be proved, got {}", obligation.status.label()));
        }
        if obligation.status == ProofConcurrencyObligationStatus::ManualPass {
            blockers.push(format!("{id}: manual_pass is not admissible proof evidence"));
        }
        validate_proof_concurrency_proof(id, &obligation.proof, blockers);
    }

    observed
}

fn obligation_label(id: &str) -> &str {
    let trimmed = id.trim();
    if trimmed.is_empty() { "<missing obligation id>" } else { trimmed }
}

fn validate_proof_concurrency_proof(
    id: &str,
    proof: &ProofConcurrencyProofInput,
    blockers: &mut Vec<String>,
) {
    if !safe_proof_concurrency_validator_identity(&proof.solver) {
        blockers.push(format!(
            "{id}: proof.solver must be a concrete non-stub local solver identity; URIs are forbidden"
        ));
    }
    for (field, value) in [
        ("certificate_sha256", proof.certificate_sha256.as_str()),
        ("transcript_sha256", proof.transcript_sha256.as_str()),
        ("dispatch_sha256", proof.dispatch_sha256.as_str()),
        ("validation_record_sha256", proof.validation_record_sha256.as_str()),
    ] {
        if !trust_types::digest::is_stable_sha256_hex(value.trim()) {
            blockers.push(format!("{id}: proof.{field} must be a canonical SHA-256 hash"));
        }
    }
    for (field, value) in [
        ("certificate_checked", proof.certificate_checked),
        ("transcript_replayed", proof.transcript_replayed),
        ("dispatch_authenticated", proof.dispatch_authenticated),
    ] {
        if !value {
            blockers.push(format!("{id}: proof.{field} must be true"));
        }
    }
}

fn canonical_proof_concurrency_source(value: &str) -> bool {
    let value = value.trim();
    if !safe_proof_concurrency_label(value)
        || value.contains("://")
        || value.to_ascii_lowercase().starts_with("urn:")
    {
        return false;
    }
    let path = Path::new(value);
    if path.is_absolute() || path.as_os_str().is_empty() {
        return false;
    }
    let mut normalized = PathBuf::new();
    for component in path.components() {
        let Component::Normal(component) = component else {
            return false;
        };
        normalized.push(component);
    }
    normalized.as_os_str() == path.as_os_str()
}

fn validate_proof_concurrency_summary(
    summary: &ProofConcurrencySummaryInput,
    observed: &ProofConcurrencySummaryInput,
    blockers: &mut Vec<String>,
) {
    for (field, declared, computed) in [
        ("total_obligations", summary.total_obligations, observed.total_obligations),
        ("proved", summary.proved, observed.proved),
        ("failed", summary.failed, observed.failed),
        ("unknown", summary.unknown, observed.unknown),
        ("skipped", summary.skipped, observed.skipped),
        ("unsupported", summary.unsupported, observed.unsupported),
        ("runtime_checked", summary.runtime_checked, observed.runtime_checked),
        ("timed_out", summary.timed_out, observed.timed_out),
        ("manual_pass", summary.manual_pass, observed.manual_pass),
    ] {
        if declared != computed {
            blockers.push(format!(
                "proof-concurrency summary.{field} declares {declared}, but obligations imply {computed}"
            ));
        }
    }
    if summary.total_obligations == 0 {
        blockers.push("proof-concurrency summary.total_obligations must be positive".to_string());
    }
    if summary.proved != summary.total_obligations {
        blockers.push(format!(
            "proof-concurrency summary must prove every obligation, got proved={} total_obligations={}",
            summary.proved, summary.total_obligations
        ));
    }
    for (field, value) in [
        ("failed", summary.failed),
        ("unknown", summary.unknown),
        ("skipped", summary.skipped),
        ("unsupported", summary.unsupported),
        ("runtime_checked", summary.runtime_checked),
        ("timed_out", summary.timed_out),
        ("manual_pass", summary.manual_pass),
    ] {
        if value != 0 {
            blockers.push(format!("proof-concurrency summary.{field} must be 0, got {value}"));
        }
    }
}

#[derive(Debug, Default)]
struct ProgramIndexRuntimeBinarySummary {
    candidate_pairs: u64,
    comparable_pairs: u64,
    runtime_speedup_geomean: Option<f64>,
    rust_binary_size_geomean: Option<f64>,
    trust_binary_size_geomean: Option<f64>,
    runtime_blockers: Vec<String>,
    binary_blockers: Vec<String>,
    clean_compile: ProgramIndexCompileSummary,
    incremental_compile: ProgramIndexCompileSummary,
}

#[derive(Debug, Default)]
struct ProgramIndexCompileSummary {
    candidate_pairs: u64,
    comparable_pairs: u64,
    rust_wall_seconds_geomean: Option<f64>,
    trust_wall_seconds_geomean: Option<f64>,
    rust_cpu_seconds_geomean: Option<f64>,
    trust_cpu_seconds_geomean: Option<f64>,
    rust_peak_rss_geomean: Option<f64>,
    trust_peak_rss_geomean: Option<f64>,
    blockers: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompileEvidenceMode {
    CleanRelease,
    IncrementalDebug,
}

impl CompileEvidenceMode {
    fn from_profile_mode(mode: &str) -> Option<Self> {
        match mode {
            "cold-artifact" => Some(Self::CleanRelease),
            "warm-incremental" => Some(Self::IncrementalDebug),
            _ => None,
        }
    }

    fn expected_profile_mode(self) -> &'static str {
        match self {
            Self::CleanRelease => "cold-artifact",
            Self::IncrementalDebug => "warm-incremental",
        }
    }

    fn expected_cache_state(self) -> &'static str {
        match self {
            Self::CleanRelease => "cold_artifact",
            Self::IncrementalDebug => "warm_incremental",
        }
    }

    fn dimension_id(self, arch: LaunchArch) -> &'static str {
        match self {
            Self::CleanRelease => arch.clean_compile_dimension_id(),
            Self::IncrementalDebug => arch.incremental_compile_dimension_id(),
        }
    }

    fn title(self, arch: LaunchArch) -> String {
        match self {
            Self::CleanRelease => format!("{} clean release compile time", arch.label()),
            Self::IncrementalDebug => format!("{} incremental debug compile time", arch.label()),
        }
    }

    fn comparison_baseline(self) -> &'static str {
        match self {
            Self::CleanRelease => {
                "rustc clean artifact compile, same source, same target, same optimization profile, no verification step"
            }
            Self::IncrementalDebug => {
                "rustc warm incremental edit-compile loop, same source and profile, no verification step"
            }
        }
    }

    fn rerun_hint(self) -> &'static str {
        match self {
            Self::CleanRelease => {
                "Rerun `targo trust benchmark program-index --compile-measurement cold-artifact --slots upstream-rustc trust-noverify`"
            }
            Self::IncrementalDebug => {
                "Rerun `targo trust benchmark program-index --compile-measurement warm-incremental --slots upstream-rustc trust-noverify`"
            }
        }
    }
}

fn read_program_index_runtime_binary_report(path: &Path) -> Result<Vec<DimensionInput>> {
    let content = read_bounded_utf8_file(path, MAX_SAVED_PROOF_REPORT_BYTES)
        .with_context(|| format!("failed to read {} safely", path.display()))?;
    let report: Value = serde_json::from_str(&content)
        .with_context(|| format!("failed to parse JSON program-index report {}", path.display()))?;

    if report.get("schema").and_then(Value::as_str) != Some(PROGRAM_INDEX_REPORT_SCHEMA) {
        bail!(
            "program-index report {} has schema {:?}, expected {PROGRAM_INDEX_REPORT_SCHEMA}",
            path.display(),
            report.get("schema").and_then(Value::as_str)
        );
    }
    validate_program_index_results_total(path, &report)?;

    let arch_detection = report_arch(&report);
    let mut target_blockers = Vec::new();
    if arch_detection.ambiguous {
        target_blockers
            .push("program-index report has conflicting target architecture metadata".to_string());
    }
    if arch_detection.arch.is_none() {
        target_blockers.push(
            "program-index report must declare target_arch/target_triple/host_arch metadata before it can classify architecture-specific launch dimensions".to_string(),
        );
    }

    let mut summary = summarize_program_index_runtime_binary_report(&report);
    summary.runtime_blockers.extend(target_blockers.iter().cloned());
    summary.binary_blockers.extend(target_blockers.iter().cloned());
    summary.clean_compile.blockers.extend(target_blockers.iter().cloned());
    summary.incremental_compile.blockers.extend(target_blockers);

    let arches = arch_detection
        .arch
        .map(|arch| vec![arch])
        .unwrap_or_else(|| vec![LaunchArch::Aarch64, LaunchArch::X86_64]);
    let mut dimensions = Vec::new();
    for arch in arches {
        if program_index_report_requests_runtime_evidence(&report) {
            dimensions.push(program_index_runtime_dimension(path, arch, &summary));
            dimensions.push(program_index_binary_size_dimension(path, arch, &summary));
        }
        let compile_modes = program_index_report_compile_modes(&report);
        if compile_modes.contains(&CompileEvidenceMode::CleanRelease) {
            dimensions.push(program_index_compile_dimension(
                path,
                arch,
                CompileEvidenceMode::CleanRelease,
                &summary.clean_compile,
            ));
        }
        if compile_modes.contains(&CompileEvidenceMode::IncrementalDebug) {
            dimensions.push(program_index_compile_dimension(
                path,
                arch,
                CompileEvidenceMode::IncrementalDebug,
                &summary.incremental_compile,
            ));
        }
    }
    Ok(dimensions)
}

fn program_index_report_requests_runtime_evidence(report: &Value) -> bool {
    let runtime_parity = report.get("runtime_parity").unwrap_or(&Value::Null);
    runtime_parity.get("requested").and_then(Value::as_bool) == Some(true)
        || runtime_parity.get("enabled").and_then(Value::as_bool) == Some(true)
        || runtime_parity.get("rows").and_then(Value::as_array).is_some_and(|rows| !rows.is_empty())
}

fn program_index_report_compile_modes(report: &Value) -> Vec<CompileEvidenceMode> {
    let mut modes = Vec::new();
    push_program_index_compile_mode(
        &mut modes,
        report.get("compile_measurement_mode").and_then(Value::as_str),
    );
    push_program_index_compile_mode(
        &mut modes,
        report
            .get("compile_measurement")
            .and_then(|value| value.get("mode"))
            .and_then(Value::as_str),
    );
    if let Some(rows) = report.get("results").and_then(Value::as_array) {
        for row in rows {
            push_program_index_compile_mode(
                &mut modes,
                row.get("measurement_profile")
                    .and_then(|profile| profile.get("mode"))
                    .and_then(Value::as_str),
            );
        }
    }
    modes
}

fn push_program_index_compile_mode(modes: &mut Vec<CompileEvidenceMode>, value: Option<&str>) {
    let Some(mode) = value.and_then(program_index_compile_mode_from_str) else {
        return;
    };
    if !modes.contains(&mode) {
        modes.push(mode);
    }
}

fn program_index_compile_mode_from_str(value: &str) -> Option<CompileEvidenceMode> {
    match value {
        "cold-artifact" => Some(CompileEvidenceMode::CleanRelease),
        "warm-incremental" => Some(CompileEvidenceMode::IncrementalDebug),
        _ => None,
    }
}

fn validate_program_index_results_total(path: &Path, report: &Value) -> Result<()> {
    let results = report
        .get("results")
        .and_then(Value::as_array)
        .with_context(|| format!("program-index report {} has no results array", path.display()))?;
    let declared_total_rows = report
        .get("summary")
        .and_then(|summary| summary.get("total_rows"))
        .and_then(Value::as_u64)
        .with_context(|| {
            format!("program-index report {} has no summary.total_rows", path.display())
        })?;
    if declared_total_rows != results.len() as u64 {
        bail!(
            "program-index report {} declares summary.total_rows={declared_total_rows}, but has {} result rows",
            path.display(),
            results.len()
        );
    }
    Ok(())
}

fn validate_strict_superiority_performance_evidence(
    report: &Value,
    observed: &mut ProgramIndexRuntimeBinarySummary,
) {
    let Some(evidence) = report.get("strict_superiority_performance_evidence") else {
        push_all_strict_performance_blockers(
            observed,
            "strict_superiority_performance_evidence must be present".to_string(),
        );
        return;
    };
    if !evidence.is_object() {
        push_all_strict_performance_blockers(
            observed,
            "strict_superiority_performance_evidence must be an object".to_string(),
        );
        return;
    }

    let report_arch = report_arch(report).arch;
    let common_blockers = strict_performance_common_blockers(report, evidence, report_arch);
    observed.clean_compile.blockers.extend(strict_performance_lane_blockers(
        evidence,
        "clean_release_compile",
        "duration_seconds",
        "release",
        Some("cold-artifact"),
        report_arch,
        &common_blockers,
    ));
    observed.incremental_compile.blockers.extend(strict_performance_lane_blockers(
        evidence,
        "incremental_debug_compile",
        "duration_seconds",
        "debug",
        Some("warm-incremental"),
        report_arch,
        &common_blockers,
    ));
    observed.runtime_blockers.extend(strict_performance_lane_blockers(
        evidence,
        "runtime_geomean",
        "run_duration_seconds",
        "release",
        None,
        report_arch,
        &common_blockers,
    ));
    observed.binary_blockers.extend(strict_performance_lane_blockers(
        evidence,
        "binary_size",
        "executable_size_bytes",
        "release",
        None,
        report_arch,
        &common_blockers,
    ));
}

fn push_all_strict_performance_blockers(
    observed: &mut ProgramIndexRuntimeBinarySummary,
    blocker: String,
) {
    observed.runtime_blockers.push(blocker.clone());
    observed.binary_blockers.push(blocker.clone());
    observed.clean_compile.blockers.push(blocker.clone());
    observed.incremental_compile.blockers.push(blocker);
}

fn strict_performance_common_blockers(
    report: &Value,
    evidence: &Value,
    report_arch: Option<LaunchArch>,
) -> Vec<String> {
    let mut blockers = Vec::new();
    if value_at(evidence, "schema") != Some(STRICT_SUPERIORITY_PERFORMANCE_SCHEMA) {
        blockers.push(format!(
            "strict_superiority_performance_evidence.schema must be {STRICT_SUPERIORITY_PERFORMANCE_SCHEMA}"
        ));
    }
    if report.get("dry_run").and_then(Value::as_bool) != Some(false)
        || evidence.get("dry_run").and_then(Value::as_bool) != Some(false)
    {
        blockers.push(
            "strict_superiority_performance_evidence must come from a non-dry-run report"
                .to_string(),
        );
    }
    let candidate_rejection = evidence.get("candidate_rejection").unwrap_or(&Value::Null);
    if candidate_rejection.get("rejected").and_then(Value::as_bool) != Some(false) {
        blockers.push(
            "strict_superiority_performance_evidence.candidate_rejection.rejected must be false"
                .to_string(),
        );
    }
    if candidate_rejection.get("admissible_for_domination").and_then(Value::as_bool) != Some(true) {
        blockers.push(
            "strict_superiority_performance_evidence.candidate_rejection.admissible_for_domination must be true"
                .to_string(),
        );
    }
    if !value_at(report, "repo_head").is_some_and(is_full_git_sha) {
        blockers.push(
            "strict_superiority_performance_evidence requires a full program-index report repo_head"
                .to_string(),
        );
    }
    if report.get("repo_dirty").and_then(Value::as_bool) != Some(false) {
        blockers.push(
            "strict_superiority_performance_evidence requires repo_dirty=false provenance"
                .to_string(),
        );
    }
    if let Some(blocker) = strict_performance_arch_blocker(
        "strict_superiority_performance_evidence.target_arch",
        evidence.get("target_arch"),
        report_arch,
    ) {
        blockers.push(blocker);
    }
    if evidence.get("lanes").and_then(Value::as_object).is_none() {
        blockers
            .push("strict_superiority_performance_evidence.lanes must be an object".to_string());
    }
    blockers
}

fn strict_performance_lane_blockers(
    evidence: &Value,
    lane_id: &str,
    metric: &str,
    required_build_profile: &str,
    required_compile_measurement_mode: Option<&str>,
    report_arch: Option<LaunchArch>,
    common_blockers: &[String],
) -> Vec<String> {
    let mut blockers = common_blockers.to_vec();
    let Some(lane) = evidence.get("lanes").and_then(|lanes| lanes.get(lane_id)) else {
        blockers.push(format!(
            "strict_superiority_performance_evidence.lanes.{lane_id} must be present"
        ));
        return blockers;
    };
    if !lane.is_object() {
        blockers.push(format!(
            "strict_superiority_performance_evidence.lanes.{lane_id} must be an object"
        ));
        return blockers;
    }

    let prefix = format!("strict_superiority_performance_evidence.lanes.{lane_id}");
    if value_at(lane, "schema") != Some(STRICT_SUPERIORITY_PERFORMANCE_SCHEMA) {
        blockers.push(format!("{prefix}.schema must be {STRICT_SUPERIORITY_PERFORMANCE_SCHEMA}"));
    }
    if value_at(lane, "lane") != Some(lane_id) {
        blockers.push(format!("{prefix}.lane must be {lane_id}"));
    }
    if value_at(lane, "status") != Some("measured") {
        blockers
            .push(format!("{prefix}.status must be measured, got {:?}", value_at(lane, "status")));
    }
    if lane.get("admissible_for_domination").and_then(Value::as_bool) != Some(true) {
        blockers.push(format!("{prefix}.admissible_for_domination must be true"));
    }
    match lane.get("blocked_reasons").and_then(Value::as_array) {
        Some(reasons) if reasons.is_empty() => {}
        Some(reasons) => {
            for reason in reasons {
                blockers.push(format!(
                    "{prefix} blocked: {}",
                    reason.as_str().unwrap_or("<non-string reason>")
                ));
            }
        }
        None => blockers.push(format!("{prefix}.blocked_reasons must be an array")),
    }
    if value_at(lane, "metric") != Some(metric) {
        blockers.push(format!("{prefix}.metric must be {metric}"));
    }
    if lane.get("lower_is_better").and_then(Value::as_bool) != Some(true) {
        blockers.push(format!("{prefix}.lower_is_better must be true"));
    }
    if value_at(lane, "required_build_profile") != Some(required_build_profile) {
        blockers.push(format!("{prefix}.required_build_profile must be {required_build_profile}"));
    }
    if value_at(lane, "actual_build_profile") != Some(required_build_profile) {
        blockers.push(format!("{prefix}.actual_build_profile must be {required_build_profile}"));
    }
    if let Some(required_mode) = required_compile_measurement_mode {
        if value_at(lane, "required_compile_measurement_mode") != Some(required_mode) {
            blockers.push(format!(
                "{prefix}.required_compile_measurement_mode must be {required_mode}"
            ));
        }
        if value_at(lane, "actual_compile_measurement_mode") != Some(required_mode) {
            blockers
                .push(format!("{prefix}.actual_compile_measurement_mode must be {required_mode}"));
        }
    }
    if let Some(blocker) = strict_performance_arch_blocker(
        &format!("{prefix}.target_arch"),
        lane.get("target_arch"),
        report_arch,
    ) {
        blockers.push(blocker);
    }
    blockers.extend(strict_performance_lane_value_blockers(lane_id, lane));
    blockers
}

fn strict_performance_arch_blocker(
    field: &str,
    value: Option<&Value>,
    expected_arch: Option<LaunchArch>,
) -> Option<String> {
    let expected_arch = expected_arch?;
    match value.and_then(Value::as_str).and_then(arch_from_text) {
        Some(actual) if actual == expected_arch => None,
        Some(actual) => Some(format!(
            "{field} must match report architecture {}, got {}",
            expected_arch.evidence_token(),
            actual.evidence_token()
        )),
        None => Some(format!(
            "{field} must declare report architecture {}",
            expected_arch.evidence_token()
        )),
    }
}

fn strict_performance_lane_value_blockers(lane_id: &str, lane: &Value) -> Vec<String> {
    let mut blockers = Vec::new();
    let prefix = format!("strict_superiority_performance_evidence.lanes.{lane_id}");
    let rust_value = positive_number_value(&lane["rust"]["value"]);
    if rust_value.is_none() {
        blockers.push(format!("{prefix}.rust.value must be a positive number"));
    }
    let trust_value = lane
        .get("trust")
        .and_then(|trust| trust.get(PROGRAM_INDEX_RUNTIME_TRUST_SLOT))
        .and_then(|trust| positive_number_value(&trust["value"]));
    if trust_value.is_none() {
        blockers.push(format!(
            "{prefix}.trust.{PROGRAM_INDEX_RUNTIME_TRUST_SLOT}.value must be a positive number"
        ));
    }
    if let (Some(rust_value), Some(trust_value)) = (rust_value, trust_value) {
        if trust_value >= rust_value {
            blockers.push(format!(
                "{prefix}: Trust value {trust_value:.6} must be strictly lower than Rust value {rust_value:.6}"
            ));
        }
    }

    let Some(comparisons) = lane.get("comparisons").and_then(Value::as_array) else {
        blockers.push(format!("{prefix}.comparisons must be an array"));
        return blockers;
    };
    if comparisons.is_empty() {
        blockers.push(format!("{prefix}.comparisons must not be empty"));
        return blockers;
    }

    let mut saw_canonical_trust_slot = false;
    for comparison in comparisons {
        let trust_slot = value_at(comparison, "trust_slot").unwrap_or("<missing>");
        if trust_slot == PROGRAM_INDEX_RUNTIME_TRUST_SLOT {
            saw_canonical_trust_slot = true;
        }
        let comparison_rust = positive_number_value(&comparison["rust_value"]);
        let comparison_trust = positive_number_value(&comparison["trust_value"]);
        if comparison_rust.is_none() || comparison_trust.is_none() {
            blockers.push(format!(
                "{prefix}.comparisons[{trust_slot}] must carry positive rust_value and trust_value"
            ));
            continue;
        }
        if comparison.get("trust_at_most_rust").and_then(Value::as_bool) != Some(true) {
            blockers.push(format!(
                "{prefix}.comparisons[{trust_slot}].trust_at_most_rust must be true"
            ));
        }
        if comparison.get("trust_strictly_better").and_then(Value::as_bool) != Some(true) {
            blockers.push(format!(
                "{prefix}.comparisons[{trust_slot}].trust_strictly_better must be true"
            ));
        }
        let rust_value = comparison_rust.expect("checked");
        let trust_value = comparison_trust.expect("checked");
        if trust_value >= rust_value {
            blockers.push(format!(
                "{prefix}.comparisons[{trust_slot}] regressed: Trust value {trust_value:.6} must be strictly lower than Rust value {rust_value:.6}"
            ));
        }
    }
    if !saw_canonical_trust_slot {
        blockers.push(format!(
            "{prefix}.comparisons must include canonical Trust slot {PROGRAM_INDEX_RUNTIME_TRUST_SLOT}"
        ));
    }
    blockers
}

fn positive_number_value(value: &Value) -> Option<f64> {
    value
        .as_f64()
        .or_else(|| value.as_i64().map(|value| value as f64))
        .or_else(|| value.as_u64().map(|value| value as f64))
        .filter(|value| value.is_finite() && *value > 0.0)
}

fn summarize_program_index_runtime_binary_report(
    report: &Value,
) -> ProgramIndexRuntimeBinarySummary {
    let mut observed = ProgramIndexRuntimeBinarySummary::default();
    if report.get("runner").and_then(|runner| runner.get("python_used")).and_then(Value::as_bool)
        != Some(false)
    {
        let blocker = "report runner must be Rust-owned with runner.python_used=false".to_string();
        observed.runtime_blockers.push(blocker.clone());
        observed.clean_compile.blockers.push(blocker.clone());
        observed.incremental_compile.blockers.push(blocker);
    }
    if report.get("dry_run").and_then(Value::as_bool) != Some(false) {
        let blocker = "program-index benchmark evidence must be a non-dry-run report".to_string();
        observed.runtime_blockers.push(blocker.clone());
        observed.clean_compile.blockers.push(blocker.clone());
        observed.incremental_compile.blockers.push(blocker);
    }
    let provenance_blockers = program_index_report_provenance_blockers(report);
    observed.runtime_blockers.extend(provenance_blockers.iter().cloned());
    observed.binary_blockers.extend(provenance_blockers.iter().cloned());
    observed.clean_compile.blockers.extend(provenance_blockers.iter().cloned());
    observed.incremental_compile.blockers.extend(provenance_blockers);
    let integrity_blockers = program_index_report_integrity_blockers(report);
    observed.runtime_blockers.extend(integrity_blockers.iter().cloned());
    observed.binary_blockers.extend(integrity_blockers.iter().cloned());
    observed.clean_compile.blockers.extend(integrity_blockers.iter().cloned());
    observed.incremental_compile.blockers.extend(integrity_blockers);
    validate_strict_superiority_performance_evidence(report, &mut observed);

    let runtime_parity = report.get("runtime_parity").unwrap_or(&Value::Null);
    if runtime_parity.get("schema").and_then(Value::as_str)
        != Some(PROGRAM_INDEX_RUNTIME_PARITY_SCHEMA)
    {
        observed
            .runtime_blockers
            .push(format!("runtime_parity.schema must be {PROGRAM_INDEX_RUNTIME_PARITY_SCHEMA}"));
    }
    if runtime_parity.get("requested").and_then(Value::as_bool) != Some(true)
        || runtime_parity.get("enabled").and_then(Value::as_bool) != Some(true)
    {
        observed.runtime_blockers.push("runtime parity must be requested and enabled".to_string());
    }
    if runtime_parity.get("status").and_then(Value::as_str) != Some("passed") {
        observed.runtime_blockers.push(format!(
            "runtime_parity.status must be passed, got {:?}",
            runtime_parity.get("status").and_then(Value::as_str)
        ));
    }
    if runtime_parity.get("baseline_slot").and_then(Value::as_str)
        != Some(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT)
    {
        observed.runtime_blockers.push(format!(
            "runtime_parity.baseline_slot must be {PROGRAM_INDEX_RUNTIME_BASELINE_SLOT}"
        ));
    }
    if json_u64(&runtime_parity["summary"], "failed") != 0
        || json_u64(&runtime_parity["summary"], "comparison_failed") != 0
    {
        observed
            .runtime_blockers
            .push("runtime parity summary must have zero failed comparison rows".to_string());
    }

    let Some(rows) = runtime_parity.get("rows").and_then(Value::as_array) else {
        observed.runtime_blockers.push("runtime_parity.rows must be an array".to_string());
        observed.binary_blockers.extend(observed.runtime_blockers.iter().cloned());
        summarize_program_index_compile_report(report, &mut observed);
        return observed;
    };
    validate_runtime_parity_summary_counts(
        &runtime_parity["summary"],
        rows,
        &mut observed.runtime_blockers,
    );
    let mut baseline_rows: BTreeMap<String, &Value> = BTreeMap::new();
    let mut trust_rows: BTreeMap<String, &Value> = BTreeMap::new();
    for row in rows {
        let Some(key) = program_index_runtime_row_key(row) else {
            continue;
        };
        match value_at(row, "slot") {
            Some(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT) => {
                if baseline_rows.insert(key.clone(), row).is_some() {
                    observed
                        .runtime_blockers
                        .push(format!("{key}: duplicate baseline runtime row"));
                }
            }
            Some(PROGRAM_INDEX_RUNTIME_TRUST_SLOT) => {
                if trust_rows.insert(key.clone(), row).is_some() {
                    observed.runtime_blockers.push(format!("{key}: duplicate Trust runtime row"));
                }
            }
            _ => {}
        }
    }
    if baseline_rows.is_empty() {
        observed.runtime_blockers.push(format!(
            "runtime parity rows must include baseline slot {PROGRAM_INDEX_RUNTIME_BASELINE_SLOT}"
        ));
    }
    if trust_rows.is_empty() {
        observed.runtime_blockers.push(format!(
            "runtime parity rows must include Trust slot {PROGRAM_INDEX_RUNTIME_TRUST_SLOT}"
        ));
    }

    let mut speedups = Vec::new();
    let mut rust_sizes = Vec::new();
    let mut trust_sizes = Vec::new();
    for missing_key in baseline_rows.keys().filter(|key| !trust_rows.contains_key(*key)) {
        observed
            .runtime_blockers
            .push(format!("{missing_key}: missing matching Trust runtime row"));
    }
    for (key, trust_row) in &trust_rows {
        let Some(baseline_row) = baseline_rows.get(key) else {
            observed.runtime_blockers.push(format!("{key}: missing matching baseline runtime row"));
            continue;
        };
        observed.candidate_pairs += 1;

        let runtime_ready =
            validate_runtime_pair(key, baseline_row, trust_row, &mut observed.runtime_blockers);
        if let (Some(rust_seconds), Some(trust_seconds)) = (
            positive_f64_at(baseline_row, "run_duration_seconds"),
            positive_f64_at(trust_row, "run_duration_seconds"),
        ) {
            if runtime_ready {
                if trust_seconds < rust_seconds {
                    speedups.push(rust_seconds / trust_seconds);
                } else {
                    observed.runtime_blockers.push(format!(
                        "{key}: Trust run_duration_seconds {trust_seconds:.6}s must be strictly less than baseline {rust_seconds:.6}s"
                    ));
                }
            }
        } else {
            observed.runtime_blockers.push(format!(
                "{key}: run_duration_seconds must be positive for baseline and Trust rows"
            ));
        }

        if runtime_ready
            && validate_binary_size_pair(
                key,
                baseline_row,
                trust_row,
                &mut observed.binary_blockers,
            )
        {
            rust_sizes.push(json_u64(baseline_row, "executable_size_bytes") as f64);
            trust_sizes.push(json_u64(trust_row, "executable_size_bytes") as f64);
        }
    }

    observed.comparable_pairs = speedups.len() as u64;
    if speedups.is_empty() {
        observed.runtime_blockers.push(
            "no comparable upstream-rustc/trust-noverify runtime pairs were present".to_string(),
        );
    } else {
        observed.runtime_speedup_geomean = geometric_mean(&speedups);
    }
    if rust_sizes.is_empty() || trust_sizes.is_empty() {
        observed
            .binary_blockers
            .push("no comparable executable size pairs were present".to_string());
    } else {
        observed.rust_binary_size_geomean = geometric_mean(&rust_sizes);
        observed.trust_binary_size_geomean = geometric_mean(&trust_sizes);
    }
    let runtime_blockers_for_binary = observed
        .runtime_blockers
        .iter()
        .filter(|blocker| {
            blocker.contains("runtime parity")
                || blocker.contains("runtime_parity")
                || blocker.contains("target")
                || blocker.contains("non-dry-run")
                || blocker.contains("runner")
        })
        .cloned()
        .collect::<Vec<_>>();
    observed.binary_blockers.extend(runtime_blockers_for_binary);
    summarize_program_index_compile_report(report, &mut observed);
    observed
}

fn summarize_program_index_compile_report(
    report: &Value,
    observed: &mut ProgramIndexRuntimeBinarySummary,
) {
    let Some(rows) = report.get("results").and_then(Value::as_array) else {
        let blocker = "program-index report results must be an array".to_string();
        observed.clean_compile.blockers.push(blocker.clone());
        observed.incremental_compile.blockers.push(blocker);
        return;
    };

    let summary_blockers = compile_resource_summary_blockers(report, rows);
    observed.clean_compile.blockers.extend(summary_blockers.iter().cloned());
    observed.incremental_compile.blockers.extend(summary_blockers);

    let mut clean_baseline_rows: BTreeMap<String, &Value> = BTreeMap::new();
    let mut clean_trust_rows: BTreeMap<String, &Value> = BTreeMap::new();
    let mut incremental_baseline_rows: BTreeMap<String, &Value> = BTreeMap::new();
    let mut incremental_trust_rows: BTreeMap<String, &Value> = BTreeMap::new();

    for row in rows {
        let Some(slot) = value_at(row, "slot") else {
            continue;
        };
        if slot != PROGRAM_INDEX_RUNTIME_BASELINE_SLOT && slot != PROGRAM_INDEX_RUNTIME_TRUST_SLOT {
            continue;
        }
        let Some(key) = program_index_runtime_row_key(row) else {
            push_compile_blocker(
                observed,
                "baseline/Trust compile row must include suite, variant, and program_id"
                    .to_string(),
            );
            continue;
        };
        let Some(mode) = compile_mode_for_row(&key, row, observed) else {
            continue;
        };
        let duplicate = match (mode, slot) {
            (CompileEvidenceMode::CleanRelease, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT) => {
                clean_baseline_rows.insert(key.clone(), row).is_some()
            }
            (CompileEvidenceMode::CleanRelease, PROGRAM_INDEX_RUNTIME_TRUST_SLOT) => {
                clean_trust_rows.insert(key.clone(), row).is_some()
            }
            (CompileEvidenceMode::IncrementalDebug, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT) => {
                incremental_baseline_rows.insert(key.clone(), row).is_some()
            }
            (CompileEvidenceMode::IncrementalDebug, PROGRAM_INDEX_RUNTIME_TRUST_SLOT) => {
                incremental_trust_rows.insert(key.clone(), row).is_some()
            }
            _ => false,
        };
        if duplicate {
            match mode {
                CompileEvidenceMode::CleanRelease => observed
                    .clean_compile
                    .blockers
                    .push(format!("{key}: duplicate {slot} clean compile measurement row")),
                CompileEvidenceMode::IncrementalDebug => observed
                    .incremental_compile
                    .blockers
                    .push(format!("{key}: duplicate {slot} incremental compile measurement row")),
            }
        }
    }

    summarize_compile_mode_pairs(
        CompileEvidenceMode::CleanRelease,
        &clean_baseline_rows,
        &clean_trust_rows,
        &mut observed.clean_compile,
    );
    summarize_compile_mode_pairs(
        CompileEvidenceMode::IncrementalDebug,
        &incremental_baseline_rows,
        &incremental_trust_rows,
        &mut observed.incremental_compile,
    );
}

fn push_compile_blocker(observed: &mut ProgramIndexRuntimeBinarySummary, blocker: String) {
    observed.clean_compile.blockers.push(blocker.clone());
    observed.incremental_compile.blockers.push(blocker);
}

fn compile_resource_summary_blockers(report: &Value, rows: &[Value]) -> Vec<String> {
    let mut blockers = Vec::new();
    let Some(summary) =
        report.get("summary").and_then(|summary| summary.get("compile_resource_usage"))
    else {
        blockers.push("summary.compile_resource_usage must be present".to_string());
        return blockers;
    };
    require_compile_summary_count(
        summary,
        "rows_with_peak_rss",
        rows.iter().filter(|row| positive_i64_at(row, "peak_rss_bytes").is_some()).count() as u64,
        &mut blockers,
    );
    require_compile_summary_count(
        summary,
        "timed_out",
        rows.iter()
            .filter(|row| row.get("timed_out").and_then(Value::as_bool) == Some(true))
            .count() as u64,
        &mut blockers,
    );

    let profiles = &summary["measurement_profiles"];
    if profiles.get("schema").and_then(Value::as_str)
        != Some(PROGRAM_INDEX_COMPILE_MEASUREMENT_PROFILE_SCHEMA)
    {
        blockers.push(format!(
            "summary.compile_resource_usage.measurement_profiles.schema must be {PROGRAM_INDEX_COMPILE_MEASUREMENT_PROFILE_SCHEMA}"
        ));
    }
    require_compile_profile_summary_count(
        profiles,
        "missing_profile_rows",
        rows.iter()
            .filter(|row| row.get("measurement_profile").and_then(Value::as_object).is_none())
            .count() as u64,
        &mut blockers,
    );
    require_compile_profile_summary_count(
        profiles,
        "incremental_rows",
        rows.iter()
            .filter(|row| {
                row["measurement_profile"].get("incremental").and_then(Value::as_bool) == Some(true)
            })
            .count() as u64,
        &mut blockers,
    );
    require_compile_profile_summary_count(
        profiles,
        "non_incremental_rows",
        rows.iter()
            .filter(|row| {
                row["measurement_profile"].get("incremental").and_then(Value::as_bool)
                    == Some(false)
            })
            .count() as u64,
        &mut blockers,
    );
    require_compile_profile_summary_count(
        profiles,
        "requested_incremental_rows",
        rows.iter()
            .filter(|row| {
                row["measurement_profile"].get("requested_incremental").and_then(Value::as_bool)
                    == Some(true)
            })
            .count() as u64,
        &mut blockers,
    );
    require_compile_profile_summary_count(
        profiles,
        "measured_incremental_rows",
        rows.iter()
            .filter(|row| {
                row["measurement_profile"].get("incremental").and_then(Value::as_bool) == Some(true)
            })
            .filter(|row| {
                row["measurement_profile"].get("status").and_then(Value::as_str) == Some("measured")
            })
            .count() as u64,
        &mut blockers,
    );
    require_compile_profile_summary_count(
        profiles,
        "measured_non_incremental_rows",
        rows.iter()
            .filter(|row| {
                row["measurement_profile"].get("incremental").and_then(Value::as_bool)
                    == Some(false)
            })
            .filter(|row| {
                row["measurement_profile"].get("status").and_then(Value::as_str) == Some("measured")
            })
            .count() as u64,
        &mut blockers,
    );
    blockers
}

fn require_compile_summary_count(
    summary: &Value,
    key: &str,
    expected: u64,
    blockers: &mut Vec<String>,
) {
    match summary.get(key).and_then(Value::as_u64) {
        Some(actual) if actual == expected => {}
        Some(actual) => blockers.push(format!(
            "summary.compile_resource_usage.{key} declares {actual}, but rows imply {expected}"
        )),
        None => blockers.push(format!("summary.compile_resource_usage.{key} must be present")),
    }
}

fn require_compile_profile_summary_count(
    profiles: &Value,
    key: &str,
    expected: u64,
    blockers: &mut Vec<String>,
) {
    match profiles.get(key).and_then(Value::as_u64) {
        Some(actual) if actual == expected => {}
        Some(actual) => blockers.push(format!(
            "summary.compile_resource_usage.measurement_profiles.{key} declares {actual}, but rows imply {expected}"
        )),
        None => blockers.push(format!(
            "summary.compile_resource_usage.measurement_profiles.{key} must be present"
        )),
    }
}

fn compile_mode_for_row(
    key: &str,
    row: &Value,
    observed: &mut ProgramIndexRuntimeBinarySummary,
) -> Option<CompileEvidenceMode> {
    let Some(profile) = row.get("measurement_profile") else {
        push_compile_blocker(
            observed,
            format!("{key}: compile row must carry measurement_profile"),
        );
        return None;
    };
    if profile.get("schema").and_then(Value::as_str)
        != Some(PROGRAM_INDEX_COMPILE_MEASUREMENT_PROFILE_SCHEMA)
    {
        push_compile_blocker(
            observed,
            format!(
                "{key}: measurement_profile.schema must be {PROGRAM_INDEX_COMPILE_MEASUREMENT_PROFILE_SCHEMA}"
            ),
        );
        return None;
    }
    if profile.get("phase").and_then(Value::as_str) != Some("compile_artifact")
        || profile.get("timing_field").and_then(Value::as_str) != Some("duration_seconds")
        || profile.get("runtime_measurements_separate").and_then(Value::as_bool) != Some(true)
    {
        push_compile_blocker(
            observed,
            format!(
                "{key}: measurement_profile must describe compile_artifact duration_seconds with runtime measurements separate"
            ),
        );
        return None;
    }
    if profile.get("status").and_then(Value::as_str) != Some("measured") {
        push_compile_blocker(
            observed,
            format!("{key}: measurement_profile.status must be measured"),
        );
        return None;
    }
    let Some(mode) = profile
        .get("mode")
        .and_then(Value::as_str)
        .and_then(CompileEvidenceMode::from_profile_mode)
    else {
        push_compile_blocker(
            observed,
            format!("{key}: measurement_profile.mode must be cold-artifact or warm-incremental"),
        );
        return None;
    };
    if let Some(blocker) = validate_compile_profile_mode(mode, key, profile) {
        match mode {
            CompileEvidenceMode::CleanRelease => observed.clean_compile.blockers.push(blocker),
            CompileEvidenceMode::IncrementalDebug => {
                observed.incremental_compile.blockers.push(blocker)
            }
        }
        return None;
    }
    Some(mode)
}

fn validate_compile_profile_mode(
    mode: CompileEvidenceMode,
    key: &str,
    profile: &Value,
) -> Option<String> {
    if profile.get("mode").and_then(Value::as_str) != Some(mode.expected_profile_mode()) {
        return Some(format!(
            "{key}: measurement_profile.mode must be {}",
            mode.expected_profile_mode()
        ));
    }
    if profile.get("cache_state").and_then(Value::as_str) != Some(mode.expected_cache_state()) {
        return Some(format!(
            "{key}: measurement_profile.cache_state must be {}",
            mode.expected_cache_state()
        ));
    }
    match mode {
        CompileEvidenceMode::CleanRelease => {
            if profile.get("requested_incremental").and_then(Value::as_bool) != Some(false)
                || profile.get("incremental").and_then(Value::as_bool) != Some(false)
            {
                return Some(format!(
                    "{key}: cold-artifact compile evidence must be non-incremental"
                ));
            }
        }
        CompileEvidenceMode::IncrementalDebug => {
            if profile.get("requested_incremental").and_then(Value::as_bool) != Some(true)
                || profile.get("incremental").and_then(Value::as_bool) != Some(true)
                || profile.get("warmup_required").and_then(Value::as_bool) != Some(true)
                || profile.get("warmup_valid").and_then(Value::as_bool) != Some(true)
            {
                return Some(format!(
                    "{key}: warm-incremental compile evidence must request incremental mode with a valid warmup"
                ));
            }
        }
    }
    None
}

fn summarize_compile_mode_pairs(
    mode: CompileEvidenceMode,
    baseline_rows: &BTreeMap<String, &Value>,
    trust_rows: &BTreeMap<String, &Value>,
    summary: &mut ProgramIndexCompileSummary,
) {
    for missing_key in baseline_rows.keys().filter(|key| !trust_rows.contains_key(*key)) {
        summary.blockers.push(format!(
            "{missing_key}: missing matching Trust {} compile row",
            mode.expected_profile_mode()
        ));
    }

    let mut rust_wall_seconds = Vec::new();
    let mut trust_wall_seconds = Vec::new();
    let mut rust_cpu_seconds = Vec::new();
    let mut trust_cpu_seconds = Vec::new();
    let mut rust_peak_rss = Vec::new();
    let mut trust_peak_rss = Vec::new();
    for (key, trust_row) in trust_rows {
        let Some(baseline_row) = baseline_rows.get(key) else {
            summary.blockers.push(format!(
                "{key}: missing matching upstream-rustc {} compile row",
                mode.expected_profile_mode()
            ));
            continue;
        };
        summary.candidate_pairs += 1;
        let Some(measurement) = validate_compile_pair(mode, key, baseline_row, trust_row, summary)
        else {
            continue;
        };
        rust_wall_seconds.push(measurement.rust_wall_seconds);
        trust_wall_seconds.push(measurement.trust_wall_seconds);
        rust_cpu_seconds.push(measurement.rust_cpu_seconds);
        trust_cpu_seconds.push(measurement.trust_cpu_seconds);
        rust_peak_rss.push(measurement.rust_peak_rss_bytes);
        trust_peak_rss.push(measurement.trust_peak_rss_bytes);
        summary.comparable_pairs += 1;
    }

    if summary.comparable_pairs == 0 {
        if summary.candidate_pairs > 0 {
            summary.blockers.push(format!(
                "no comparable upstream-rustc/trust-noverify {} compile pairs were present",
                mode.expected_profile_mode()
            ));
        }
        return;
    }
    summary.rust_wall_seconds_geomean = geometric_mean(&rust_wall_seconds);
    summary.trust_wall_seconds_geomean = geometric_mean(&trust_wall_seconds);
    summary.rust_cpu_seconds_geomean = geometric_mean(&rust_cpu_seconds);
    summary.trust_cpu_seconds_geomean = geometric_mean(&trust_cpu_seconds);
    summary.rust_peak_rss_geomean = geometric_mean(&rust_peak_rss);
    summary.trust_peak_rss_geomean = geometric_mean(&trust_peak_rss);
}

#[derive(Debug)]
struct CompilePairMeasurement {
    rust_wall_seconds: f64,
    trust_wall_seconds: f64,
    rust_cpu_seconds: f64,
    trust_cpu_seconds: f64,
    rust_peak_rss_bytes: f64,
    trust_peak_rss_bytes: f64,
}

fn validate_compile_pair(
    mode: CompileEvidenceMode,
    key: &str,
    baseline_row: &Value,
    trust_row: &Value,
    summary: &mut ProgramIndexCompileSummary,
) -> Option<CompilePairMeasurement> {
    let mut ready = true;
    if !validate_program_source_identity(
        key,
        "compile",
        baseline_row,
        trust_row,
        &mut summary.blockers,
    ) {
        ready = false;
    }
    for field in ["expected", "slot_mode"] {
        if !matching_nonempty_string_field(baseline_row, trust_row, field) {
            summary.blockers.push(format!(
                "{key}: compile input identity field {field} must be present and equal"
            ));
            ready = false;
        }
    }
    for (label, row, slot) in [
        ("baseline", baseline_row, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT),
        ("Trust", trust_row, PROGRAM_INDEX_RUNTIME_TRUST_SLOT),
    ] {
        if value_at(row, "slot") != Some(slot) {
            summary.blockers.push(format!("{key}: {label} compile row slot must be {slot}"));
            ready = false;
        }
        if value_at(row, "outcome") != Some("passed")
            || value_at(row, "observed") != Some("compile_pass")
        {
            summary.blockers.push(format!(
                "{key}: {label} compile row must have outcome=passed and observed=compile_pass"
            ));
            ready = false;
        }
        if row.get("timed_out").and_then(Value::as_bool) != Some(false) {
            summary.blockers.push(format!("{key}: {label} compile row must not time out"));
            ready = false;
        }
        let Some(profile) = row.get("measurement_profile") else {
            summary.blockers.push(format!("{key}: {label} row missing measurement_profile"));
            ready = false;
            continue;
        };
        if let Some(blocker) = validate_compile_profile_mode(mode, key, profile) {
            summary.blockers.push(format!("{key}: {label} {blocker}"));
            ready = false;
        }
        if !validate_compile_resource_usage_binding(mode, key, label, slot, row, summary) {
            ready = false;
        }
    }

    let rust_wall_seconds = match positive_f64_at(baseline_row, "duration_seconds") {
        Some(value) => value,
        None => {
            summary.blockers.push(format!(
                "{key}: baseline duration_seconds must be positive{}",
                compile_row_context_suffix(mode, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT)
            ));
            return None;
        }
    };
    let trust_wall_seconds = match positive_f64_at(trust_row, "duration_seconds") {
        Some(value) => value,
        None => {
            summary.blockers.push(format!(
                "{key}: Trust duration_seconds must be positive{}",
                compile_row_context_suffix(mode, PROGRAM_INDEX_RUNTIME_TRUST_SLOT)
            ));
            return None;
        }
    };
    let rust_cpu_seconds = match positive_cpu_seconds(baseline_row) {
        Some(value) => value,
        None => {
            summary.blockers.push(format!(
                "{key}: baseline resource_usage user_cpu_seconds/system_cpu_seconds must be present{}",
                compile_row_context_suffix(mode, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT)
            ));
            return None;
        }
    };
    let trust_cpu_seconds = match positive_cpu_seconds(trust_row) {
        Some(value) => value,
        None => {
            summary.blockers.push(format!(
                "{key}: Trust resource_usage user_cpu_seconds/system_cpu_seconds must be present{}",
                compile_row_context_suffix(mode, PROGRAM_INDEX_RUNTIME_TRUST_SLOT)
            ));
            return None;
        }
    };
    let rust_peak_rss_bytes = match positive_i64_at(baseline_row, "peak_rss_bytes") {
        Some(value) => value as f64,
        None => {
            summary.blockers.push(format!(
                "{key}: baseline peak_rss_bytes must be positive{}",
                compile_row_context_suffix(mode, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT)
            ));
            return None;
        }
    };
    let trust_peak_rss_bytes = match positive_i64_at(trust_row, "peak_rss_bytes") {
        Some(value) => value as f64,
        None => {
            summary.blockers.push(format!(
                "{key}: Trust peak_rss_bytes must be positive{}",
                compile_row_context_suffix(mode, PROGRAM_INDEX_RUNTIME_TRUST_SLOT)
            ));
            return None;
        }
    };

    if trust_wall_seconds >= rust_wall_seconds {
        summary.blockers.push(format!(
            "{key}: Trust wall compile time {trust_wall_seconds:.6}s must beat rustc {rust_wall_seconds:.6}s"
        ));
        ready = false;
    }
    if trust_cpu_seconds >= rust_cpu_seconds {
        summary.blockers.push(format!(
            "{key}: Trust compile CPU time {trust_cpu_seconds:.6}s must beat rustc {rust_cpu_seconds:.6}s"
        ));
        ready = false;
    }
    if trust_peak_rss_bytes >= rust_peak_rss_bytes {
        summary.blockers.push(format!(
            "{key}: Trust peak RSS {trust_peak_rss_bytes:.0} bytes must beat rustc {rust_peak_rss_bytes:.0} bytes"
        ));
        ready = false;
    }

    ready.then_some(CompilePairMeasurement {
        rust_wall_seconds,
        trust_wall_seconds,
        rust_cpu_seconds,
        trust_cpu_seconds,
        rust_peak_rss_bytes,
        trust_peak_rss_bytes,
    })
}

fn validate_compile_resource_usage_binding(
    mode: CompileEvidenceMode,
    key: &str,
    label: &str,
    slot: &str,
    row: &Value,
    summary: &mut ProgramIndexCompileSummary,
) -> bool {
    let context = compile_row_context_suffix(mode, slot);
    let Some(usage) = row.get("resource_usage") else {
        summary.blockers.push(format!("{key}: {label} row missing resource_usage{context}"));
        return false;
    };

    let mut ready = true;
    if value_at(usage, "source") != Some(PROGRAM_INDEX_COMPILE_RESOURCE_USAGE_SOURCE) {
        summary.blockers.push(format!(
            "{key}: {label} resource_usage.source must be {PROGRAM_INDEX_COMPILE_RESOURCE_USAGE_SOURCE} for compile resource evidence{context}"
        ));
        ready = false;
    }

    match positive_f64_at(usage, "elapsed_seconds") {
        Some(elapsed_seconds) => {
            if let Some(duration_seconds) = positive_f64_at(row, "duration_seconds") {
                let delta = (duration_seconds - elapsed_seconds).abs();
                if delta > PROGRAM_INDEX_COMPILE_RESOURCE_SECONDS_TOLERANCE {
                    summary.blockers.push(format!(
                        "{key}: {label} duration_seconds {duration_seconds:.6}s must match resource_usage.elapsed_seconds {elapsed_seconds:.6}s{context}"
                    ));
                    ready = false;
                }
            }
        }
        None => {
            summary.blockers.push(format!(
                "{key}: {label} resource_usage.elapsed_seconds must be positive{context}"
            ));
            ready = false;
        }
    }

    let resource_peak_rss = match positive_i64_at(usage, "peak_rss_bytes") {
        Some(resource_peak_rss) => {
            if let Some(row_peak_rss) = positive_i64_at(row, "peak_rss_bytes") {
                if row_peak_rss != resource_peak_rss {
                    summary.blockers.push(format!(
                        "{key}: {label} peak_rss_bytes {row_peak_rss} must match resource_usage.peak_rss_bytes {resource_peak_rss}{context}"
                    ));
                    ready = false;
                }
            }
            Some(resource_peak_rss)
        }
        None => {
            summary.blockers.push(format!(
                "{key}: {label} resource_usage.peak_rss_bytes must be positive{context}"
            ));
            ready = false;
            None
        }
    };

    let peak_rss_raw = match positive_i64_at(usage, "peak_rss_raw") {
        Some(value) => Some(value),
        None => {
            summary.blockers.push(format!(
                "{key}: {label} resource_usage.peak_rss_raw must be positive{context}"
            ));
            ready = false;
            None
        }
    };
    let peak_rss_raw_unit = match value_at(usage, "peak_rss_raw_unit") {
        Some(unit) if compile_peak_rss_raw_unit_is_valid(unit) => Some(unit),
        Some(unit) => {
            summary.blockers.push(format!(
                "{key}: {label} resource_usage.peak_rss_raw_unit must be bytes or kilobytes, got `{unit}`{context}"
            ));
            ready = false;
            None
        }
        None => {
            summary.blockers.push(format!(
                "{key}: {label} resource_usage.peak_rss_raw_unit must be bytes or kilobytes{context}"
            ));
            ready = false;
            None
        }
    };
    if let (Some(resource_peak_rss), Some(raw), Some(unit)) =
        (resource_peak_rss, peak_rss_raw, peak_rss_raw_unit)
    {
        match normalize_compile_peak_rss_raw(raw, unit) {
            Some(normalized) if normalized == resource_peak_rss => {}
            Some(normalized) => {
                summary.blockers.push(format!(
                    "{key}: {label} resource_usage.peak_rss_bytes {resource_peak_rss} must match peak_rss_raw {raw} {unit} normalized to {normalized}{context}"
                ));
                ready = false;
            }
            None => {
                summary.blockers.push(format!(
                    "{key}: {label} resource_usage.peak_rss_raw {raw} {unit} overflows normalized bytes{context}"
                ));
                ready = false;
            }
        }
    }

    ready
}

fn compile_peak_rss_raw_unit_is_valid(unit: &str) -> bool {
    matches!(unit, "bytes" | "kilobytes")
}

fn normalize_compile_peak_rss_raw(raw: i64, unit: &str) -> Option<i64> {
    match unit {
        "bytes" => Some(raw),
        "kilobytes" => raw.checked_mul(1024),
        _ => None,
    }
}

fn compile_row_context_suffix(mode: CompileEvidenceMode, slot: &str) -> String {
    format!(" (slot={slot} measurement_profile.mode={})", mode.expected_profile_mode())
}

fn validate_runtime_parity_summary_counts(
    summary: &Value,
    rows: &[Value],
    blockers: &mut Vec<String>,
) {
    require_runtime_parity_summary_count(summary, "total_rows", rows.len() as u64, blockers);
    require_runtime_parity_summary_count(
        summary,
        "passed",
        runtime_parity_classification_count(rows, "runtime-parity", None),
        blockers,
    );
    require_runtime_parity_summary_count(
        summary,
        "failed",
        runtime_parity_classification_count(rows, "runtime-divergence", None),
        blockers,
    );
    require_runtime_parity_summary_count(
        summary,
        "not_applicable",
        runtime_parity_classification_count(rows, "runtime-not-applicable", None),
        blockers,
    );
    require_runtime_parity_summary_count(
        summary,
        "known_gap",
        runtime_parity_classification_count(rows, "runtime-known-gap", None),
        blockers,
    );
    require_runtime_parity_summary_count(
        summary,
        "baseline_passed",
        runtime_parity_classification_count(
            rows,
            "runtime-parity",
            Some(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT),
        ),
        blockers,
    );
    require_runtime_parity_summary_count(
        summary,
        "comparison_passed",
        rows.iter()
            .filter(|row| value_at(row, "slot") != Some(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT))
            .filter(|row| value_at(row, "runtime_classification") == Some("runtime-parity"))
            .count() as u64,
        blockers,
    );
    require_runtime_parity_summary_count(
        summary,
        "comparison_failed",
        rows.iter()
            .filter(|row| value_at(row, "slot") != Some(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT))
            .filter(|row| value_at(row, "runtime_classification") == Some("runtime-divergence"))
            .count() as u64,
        blockers,
    );
}

fn runtime_parity_classification_count(
    rows: &[Value],
    classification: &str,
    slot: Option<&str>,
) -> u64 {
    rows.iter()
        .filter(|row| value_at(row, "runtime_classification") == Some(classification))
        .filter(|row| match slot {
            Some(slot) => value_at(row, "slot") == Some(slot),
            None => true,
        })
        .count() as u64
}

fn require_runtime_parity_summary_count(
    summary: &Value,
    key: &str,
    expected: u64,
    blockers: &mut Vec<String>,
) {
    match summary.get(key).and_then(Value::as_u64) {
        Some(actual) if actual == expected => {}
        Some(actual) => blockers.push(format!(
            "runtime_parity.summary.{key} declares {actual}, but rows imply {expected}"
        )),
        None => blockers.push(format!(
            "runtime_parity.summary.{key} must be present and match runtime_parity.rows"
        )),
    }
}

fn program_index_report_provenance_blockers(report: &Value) -> Vec<String> {
    let mut blockers = Vec::new();
    match value_at(report, "repo_head") {
        Some(head) if is_full_git_sha(head) => {}
        Some(head) => blockers
            .push(format!("program-index report repo_head must be a full git SHA, got `{head}`")),
        None => blockers.push(
            "program-index report must include repo_head for reviewed-commit provenance"
                .to_string(),
        ),
    }
    match report.get("repo_dirty").and_then(Value::as_bool) {
        Some(false) => {}
        Some(true) => blockers.push(
            "program-index report repo_dirty must be false for golden-path evidence".to_string(),
        ),
        None => blockers.push(
            "program-index report must include repo_dirty=false for golden-path evidence"
                .to_string(),
        ),
    }
    let metadata = report.get("repo_dirty_metadata").unwrap_or(&Value::Null);
    if metadata.get("available").and_then(Value::as_bool) != Some(true) {
        blockers.push(
            "program-index report must include repo_dirty_metadata.available=true".to_string(),
        );
    }
    if metadata.get("dirty").and_then(Value::as_bool) != Some(false) {
        blockers
            .push("program-index report must include repo_dirty_metadata.dirty=false".to_string());
    }
    match value_at(metadata, "untracked_files") {
        Some("all") => {}
        Some("included") => blockers.push(
            "program-index report repo_dirty_metadata.untracked_files must be all, not included"
                .to_string(),
        ),
        _ => blockers.push(
            "program-index report repo_dirty_metadata must include untracked_files=all".to_string(),
        ),
    }
    if value_at(metadata, "ignore_submodules") != Some("none") {
        blockers.push(
            "program-index report repo_dirty_metadata must include ignore_submodules=none"
                .to_string(),
        );
    }
    blockers
}

fn program_index_report_integrity_blockers(report: &Value) -> Vec<String> {
    let mut blockers = Vec::new();
    let upstream = report.get("upstream_baseline").unwrap_or(&Value::Null);
    match value_at(upstream, "status") {
        Some("passed") => {}
        Some(status) => blockers
            .push(format!("program-index upstream_baseline.status must be passed, got `{status}`")),
        None => blockers
            .push("program-index report must include upstream_baseline.status=passed".to_string()),
    }
    let entries = upstream.get("entries").and_then(Value::as_array).cloned().unwrap_or_default();
    if entries.is_empty() {
        blockers.push(
            "program-index upstream_baseline.entries must include the external upstream-rustc binding"
                .to_string(),
        );
    }
    if !entries
        .iter()
        .any(|entry| value_at(entry, "slot") == Some(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT))
    {
        blockers.push(format!(
            "program-index upstream_baseline.entries must include slot {PROGRAM_INDEX_RUNTIME_BASELINE_SLOT}"
        ));
    }
    for entry in entries
        .iter()
        .filter(|entry| value_at(entry, "slot") == Some(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT))
    {
        validate_program_index_upstream_baseline_entry(report, entry, &mut blockers);
    }

    match report.get("toolchain_integrity").and_then(|value| value_at(value, "status")) {
        Some("unchanged") => {}
        Some(status) => blockers.push(format!(
            "program-index toolchain_integrity.status must be unchanged, got `{status}`"
        )),
        None => blockers.push(
            "program-index report must include toolchain_integrity.status=unchanged".to_string(),
        ),
    }
    match report.get("stage2_preflight").and_then(|value| value_at(value, "status")) {
        Some("ready") => {}
        Some(status) => blockers
            .push(format!("program-index stage2_preflight.status must be ready, got `{status}`")),
        None => blockers
            .push("program-index report must include stage2_preflight.status=ready".to_string()),
    }
    match report.get("trust_unlock_path").and_then(|value| value_at(value, "status")) {
        Some("ready_for_trust_compile_evidence") => {}
        Some(status) => blockers.push(format!(
            "program-index trust_unlock_path.status must be ready_for_trust_compile_evidence, got `{status}`"
        )),
        None => blockers.push(
            "program-index report must include trust_unlock_path.status=ready_for_trust_compile_evidence"
                .to_string(),
        ),
    }
    if !program_index_slot_binding_declared(report, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT) {
        blockers.push(format!(
            "program-index slot_bindings must include {PROGRAM_INDEX_RUNTIME_BASELINE_SLOT}"
        ));
    }
    if !program_index_slot_binding_declared(report, PROGRAM_INDEX_RUNTIME_TRUST_SLOT) {
        blockers.push(format!(
            "program-index slot_bindings must include {PROGRAM_INDEX_RUNTIME_TRUST_SLOT}"
        ));
    }
    blockers
}

fn validate_program_index_upstream_baseline_entry(
    report: &Value,
    entry: &Value,
    blockers: &mut Vec<String>,
) {
    match value_at(entry, "status") {
        Some("passed") => {}
        Some(status) => blockers.push(format!(
            "program-index upstream-rustc baseline entry status must be passed, got `{status}`"
        )),
        None => blockers.push(
            "program-index upstream-rustc baseline entry must include status=passed".to_string(),
        ),
    }
    let version_probe = entry.get("version_probe").unwrap_or(&Value::Null);
    validate_program_index_probe_status("upstream-rustc -vV", version_probe, blockers);
    let version_text = program_index_probe_text(version_probe);
    if program_index_probe_field(&version_text, "binary").as_deref() != Some("rustc") {
        blockers.push("upstream-rustc -vV must declare `binary: rustc`".to_string());
    }
    match program_index_probe_field(&version_text, "commit-hash") {
        Some(commit) if is_full_git_sha(&commit) => {}
        Some(commit) => blockers
            .push(format!("upstream-rustc -vV commit-hash must be a full git SHA, got `{commit}`")),
        None => blockers.push("upstream-rustc -vV must declare commit-hash".to_string()),
    }
    for field in ["host", "release"] {
        if program_index_probe_field(&version_text, field).as_deref().is_none_or(str::is_empty) {
            blockers.push(format!("upstream-rustc -vV must declare {field}"));
        }
    }

    let sysroot_probe = entry.get("sysroot_probe").unwrap_or(&Value::Null);
    validate_program_index_probe_status("upstream-rustc --print sysroot", sysroot_probe, blockers);
    let sysroot_text = program_index_probe_text(sysroot_probe);
    let sysroot = sysroot_text.lines().next().map(str::trim).unwrap_or("");
    if sysroot.is_empty() {
        blockers.push("upstream-rustc --print sysroot must emit a nonempty sysroot".to_string());
    } else if let Some(repo_root) = value_at(report, "repo_root") {
        let repo_root = Path::new(repo_root);
        let sysroot_path = Path::new(sysroot);
        let sysroot_path = if sysroot_path.is_absolute() {
            sysroot_path.to_path_buf()
        } else {
            repo_root.join(sysroot_path)
        };
        if path_is_inside(&sysroot_path, repo_root) {
            blockers.push(
                "upstream-rustc --print sysroot must not resolve inside this Trust checkout"
                    .to_string(),
            );
        }
    }
}

fn validate_program_index_probe_status(label: &str, probe: &Value, blockers: &mut Vec<String>) {
    match value_at(probe, "status") {
        Some("available") => {}
        Some(status) => {
            blockers.push(format!("{label} probe status must be available, got `{status}`"))
        }
        None => blockers.push(format!("{label} probe must include status=available")),
    }
    if probe.get("trust_marker").and_then(Value::as_bool) == Some(true) {
        blockers.push(format!("{label} probe must not declare Trust identity"));
    }
}

fn program_index_probe_text(probe: &Value) -> String {
    [probe.get("stdout"), probe.get("stderr")]
        .into_iter()
        .filter_map(|value| value.and_then(Value::as_str))
        .filter(|value| !value.trim().is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

fn program_index_probe_field(text: &str, field: &str) -> Option<String> {
    let prefix = format!("{field}:");
    text.lines()
        .find_map(|line| line.trim().strip_prefix(&prefix).map(str::trim))
        .filter(|value| !value.is_empty())
        .map(str::to_string)
}

fn program_index_slot_binding_declared(report: &Value, slot: &str) -> bool {
    report.get("slot_bindings").and_then(Value::as_array).is_some_and(|bindings| {
        bindings.iter().any(|binding| value_at(binding, "slot") == Some(slot))
    })
}

fn path_is_inside(path: &Path, root: &Path) -> bool {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let root = root.canonicalize().unwrap_or_else(|_| root.to_path_buf());
    path.starts_with(root)
}

fn is_full_git_sha(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn text_contains_full_git_sha(value: &str) -> bool {
    value.split(|ch: char| !ch.is_ascii_hexdigit()).any(is_full_git_sha)
}


fn program_index_runtime_row_key(row: &Value) -> Option<String> {
    let program = value_at(row, "program_id")?;
    let suite = value_at(row, "suite").unwrap_or("<unknown-suite>");
    let variant = value_at(row, "variant").unwrap_or("<unknown-variant>");
    Some(format!("{suite}:{variant}:{program}"))
}

fn validate_runtime_pair(
    key: &str,
    baseline_row: &Value,
    trust_row: &Value,
    blockers: &mut Vec<String>,
) -> bool {
    let mut ready = true;
    if !validate_program_source_identity(key, "runtime", baseline_row, trust_row, blockers) {
        ready = false;
    }
    for (label, row, slot) in [
        ("baseline", baseline_row, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT),
        ("Trust", trust_row, PROGRAM_INDEX_RUNTIME_TRUST_SLOT),
    ] {
        if value_at(row, "slot") != Some(slot) {
            blockers.push(format!("{key}: {label} row slot must be {slot}"));
            ready = false;
        }
        if row.get("runtime_participant").and_then(Value::as_bool) != Some(true) {
            blockers.push(format!("{key}: {label} row must be a runtime participant"));
            ready = false;
        }
        if value_at(row, "build_status") != Some("compile_pass")
            || value_at(row, "run_status") != Some("run_complete")
        {
            blockers.push(format!("{key}: {label} row must compile and run to completion"));
            ready = false;
        }
        if value_at(row, "runtime_classification") != Some("runtime-parity") {
            blockers.push(format!("{key}: {label} row must be classified runtime-parity"));
            ready = false;
        }
        if canonical_sha256_at(row, "run_stdout_sha256").is_none()
            || runtime_stderr_hash(row).is_none()
        {
            blockers.push(format!(
                "{key}: {label} row must carry canonical runtime stdout/stderr SHA-256 hashes"
            ));
            ready = false;
        }
    }
    for field in ["run_exit_code", "run_stdout_sha256"] {
        if baseline_row.get(field) != trust_row.get(field) {
            blockers.push(format!("{key}: runtime parity field {field} differs"));
            ready = false;
        }
    }
    if runtime_stderr_hash(baseline_row) != runtime_stderr_hash(trust_row) {
        blockers.push(format!("{key}: runtime stderr hash differs"));
        ready = false;
    }
    ready
}

fn validate_binary_size_pair(
    key: &str,
    baseline_row: &Value,
    trust_row: &Value,
    blockers: &mut Vec<String>,
) -> bool {
    let mut ready = true;
    if !validate_program_source_identity(key, "binary-size", baseline_row, trust_row, blockers) {
        ready = false;
    }
    for (label, row) in [("baseline", baseline_row), ("Trust", trust_row)] {
        if json_u64(row, "executable_size_bytes") == 0 {
            blockers.push(format!("{key}: {label} executable_size_bytes must be nonzero"));
            ready = false;
        }
        if canonical_sha256_at(row, "executable_sha256").is_none() {
            blockers
                .push(format!("{key}: {label} executable_sha256 must be a canonical SHA-256 hash"));
            ready = false;
        }
    }
    let baseline_size = json_u64(baseline_row, "executable_size_bytes");
    let trust_size = json_u64(trust_row, "executable_size_bytes");
    if baseline_size > 0 && trust_size > 0 && trust_size >= baseline_size {
        blockers.push(format!(
            "{key}: Trust executable_size_bytes {trust_size} must be strictly smaller than baseline {baseline_size}"
        ));
        ready = false;
    }
    ready
}

fn validate_program_source_identity(
    key: &str,
    evidence_kind: &str,
    baseline_row: &Value,
    trust_row: &Value,
    blockers: &mut Vec<String>,
) -> bool {
    let mut ready = true;
    for (label, row) in [("baseline", baseline_row), ("Trust", trust_row)] {
        if canonical_sha256_at(row, "source_sha256").is_none() {
            blockers.push(format!(
                "{key}: {label} {evidence_kind} row must carry canonical source_sha256"
            ));
            ready = false;
        }
        for field in ["program_id", "pair_id", "variant", "suite", "source"] {
            if !value_at(row, field).is_some_and(|value| !value.trim().is_empty()) {
                blockers.push(format!(
                    "{key}: {label} {evidence_kind} row must carry nonempty {field}"
                ));
                ready = false;
            }
        }
    }
    for field in ["program_id", "pair_id", "variant", "suite", "source", "source_sha256"] {
        if !matching_nonempty_string_field(baseline_row, trust_row, field) {
            blockers.push(format!(
                "{key}: {evidence_kind} source identity field {field} must be present and equal"
            ));
            ready = false;
        }
    }
    ready
}

fn matching_nonempty_string_field(left: &Value, right: &Value, field: &str) -> bool {
    match (value_at(left, field), value_at(right, field)) {
        (Some(left), Some(right)) => !left.trim().is_empty() && left == right,
        _ => false,
    }
}

fn runtime_stderr_hash(row: &Value) -> Option<&str> {
    canonical_sha256_at(row, "run_stderr_normalized_sha256")
        .or_else(|| canonical_sha256_at(row, "run_stderr_sha256"))
}

fn positive_f64_at(value: &Value, key: &str) -> Option<f64> {
    let number = value.get(key).and_then(Value::as_f64)?;
    (number.is_finite() && number > 0.0).then_some(number)
}

fn nonnegative_f64_at(value: &Value, key: &str) -> Option<f64> {
    let number = value.get(key).and_then(Value::as_f64)?;
    (number.is_finite() && number >= 0.0).then_some(number)
}

fn positive_i64_at(value: &Value, key: &str) -> Option<i64> {
    let number = value.get(key).and_then(Value::as_i64)?;
    (number > 0).then_some(number)
}

fn positive_cpu_seconds(row: &Value) -> Option<f64> {
    let usage = row.get("resource_usage")?;
    let user = nonnegative_f64_at(usage, "user_cpu_seconds")?;
    let system = nonnegative_f64_at(usage, "system_cpu_seconds")?;
    let total = user + system;
    (total.is_finite() && total > 0.0).then_some(total)
}

fn nonempty_value_at<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value_at(value, key).map(str::trim).filter(|value| !value.is_empty())
}

fn canonical_sha256_at<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    nonempty_value_at(value, key).filter(|value| trust_types::digest::is_stable_sha256_hex(value))
}

fn geometric_mean(values: &[f64]) -> Option<f64> {
    if values.is_empty() || values.iter().any(|value| !value.is_finite() || *value <= 0.0) {
        return None;
    }
    Some((values.iter().map(|value| value.ln()).sum::<f64>() / values.len() as f64).exp())
}

fn program_index_runtime_dimension(
    path: &Path,
    arch: LaunchArch,
    summary: &ProgramIndexRuntimeBinarySummary,
) -> DimensionInput {
    let measured = summary.runtime_blockers.is_empty()
        && summary.runtime_speedup_geomean.is_some()
        && summary.comparable_pairs > 0;
    let status = if measured {
        None
    } else if summary.candidate_pairs == 0 && summary.runtime_blockers.is_empty() {
        Some(DeclaredStatus::Unknown)
    } else {
        Some(DeclaredStatus::Fail)
    };
    DimensionInput {
        id: arch.runtime_dimension_id().to_string(),
        title: format!("{} compiled-program runtime geomean", arch.label()),
        category: DimensionCategory::Performance,
        metric: Some(MetricKind::Throughput),
        comparison_baseline: Some(
            "programs compiled by rustc with the same sources, target CPU, linker, flags, and profile"
                .to_string(),
        ),
        required: true,
        rust_value: measured.then_some(1.0),
        trust_value: if measured { summary.runtime_speedup_geomean } else { None },
        higher_is_better: Some(true),
        min_trust_delta_pct: Some(0.000001),
        max_trust_regression_pct: None,
        status,
        unit: Some("geomean_speedup".to_string()),
        weight: 1.0,
        evidence: vec![format!(
            "{}: schema={} runtime_schema={} target_arch={} baseline_slot={} trust_slot={} candidate_pairs={} comparable_pairs={} geomean_speedup={} blockers={}",
            path.display(),
            PROGRAM_INDEX_REPORT_SCHEMA,
            PROGRAM_INDEX_RUNTIME_PARITY_SCHEMA,
            arch.evidence_token(),
            PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
            PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
            summary.candidate_pairs,
            summary.comparable_pairs,
            summary.runtime_speedup_geomean.map(|value| format!("{value:.6}")).unwrap_or_else(|| "n/a".to_string()),
            summary.runtime_blockers.len()
        )],
        ai_hint: Some(if measured {
            "Keep the program-index runtime parity report fresh for the reviewed commit."
                .to_string()
        } else {
            format!(
                "Rerun `targo trust benchmark program-index --runtime-parity --slots {PROGRAM_INDEX_RUNTIME_BASELINE_SLOT} {PROGRAM_INDEX_RUNTIME_TRUST_SLOT}` with clean target metadata. Blockers: {}",
                summary.runtime_blockers.join("; ")
            )
        }),
        owner: None,
        evidence_source: DimensionEvidenceSource::ProgramIndexRuntimeBinaryReport,
    }
}

fn program_index_binary_size_dimension(
    path: &Path,
    arch: LaunchArch,
    summary: &ProgramIndexRuntimeBinarySummary,
) -> DimensionInput {
    let measured = summary.binary_blockers.is_empty()
        && summary.rust_binary_size_geomean.is_some()
        && summary.trust_binary_size_geomean.is_some()
        && summary.comparable_pairs > 0;
    let status = if measured {
        None
    } else if summary.candidate_pairs == 0 && summary.binary_blockers.is_empty() {
        Some(DeclaredStatus::Unknown)
    } else {
        Some(DeclaredStatus::Fail)
    };
    DimensionInput {
        id: arch.binary_size_dimension_id().to_string(),
        title: format!("{} generated binary size", arch.label()),
        category: DimensionCategory::Performance,
        metric: Some(MetricKind::BinarySizeBytes),
        comparison_baseline: Some(
            "rustc-generated binaries with identical source, target, flags, profile, strip/debug settings"
                .to_string(),
        ),
        required: true,
        rust_value: if measured { summary.rust_binary_size_geomean } else { None },
        trust_value: if measured { summary.trust_binary_size_geomean } else { None },
        higher_is_better: Some(false),
        min_trust_delta_pct: Some(0.000001),
        max_trust_regression_pct: None,
        status,
        unit: Some("bytes_geomean".to_string()),
        weight: 1.0,
        evidence: vec![format!(
            "{}: schema={} runtime_schema={} target_arch={} baseline_slot={} trust_slot={} candidate_pairs={} comparable_pairs={} rust_binary_size_geomean={} trust_binary_size_geomean={} blockers={}",
            path.display(),
            PROGRAM_INDEX_REPORT_SCHEMA,
            PROGRAM_INDEX_RUNTIME_PARITY_SCHEMA,
            arch.evidence_token(),
            PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
            PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
            summary.candidate_pairs,
            summary.comparable_pairs,
            summary.rust_binary_size_geomean.map(|value| format!("{value:.3}")).unwrap_or_else(|| "n/a".to_string()),
            summary.trust_binary_size_geomean.map(|value| format!("{value:.3}")).unwrap_or_else(|| "n/a".to_string()),
            summary.binary_blockers.len()
        )],
        ai_hint: Some(if measured {
            "Keep executable-size evidence tied to runtime-parity rows for the reviewed commit."
                .to_string()
        } else {
            format!(
                "Rerun program-index runtime parity with executable hashes and sizes for {PROGRAM_INDEX_RUNTIME_BASELINE_SLOT} and {PROGRAM_INDEX_RUNTIME_TRUST_SLOT}. Blockers: {}",
                summary.binary_blockers.join("; ")
            )
        }),
        owner: None,
        evidence_source: DimensionEvidenceSource::ProgramIndexRuntimeBinaryReport,
    }
}

fn program_index_compile_dimension(
    path: &Path,
    arch: LaunchArch,
    mode: CompileEvidenceMode,
    summary: &ProgramIndexCompileSummary,
) -> DimensionInput {
    let measured = summary.blockers.is_empty()
        && summary.rust_wall_seconds_geomean.is_some()
        && summary.trust_wall_seconds_geomean.is_some()
        && summary.rust_cpu_seconds_geomean.is_some()
        && summary.trust_cpu_seconds_geomean.is_some()
        && summary.rust_peak_rss_geomean.is_some()
        && summary.trust_peak_rss_geomean.is_some()
        && summary.comparable_pairs > 0;
    let status = if measured {
        None
    } else if summary.candidate_pairs == 0 && summary.blockers.is_empty() {
        Some(DeclaredStatus::Unknown)
    } else {
        Some(DeclaredStatus::Fail)
    };
    DimensionInput {
        id: mode.dimension_id(arch).to_string(),
        title: mode.title(arch),
        category: DimensionCategory::Performance,
        metric: Some(MetricKind::LatencyMs),
        comparison_baseline: Some(mode.comparison_baseline().to_string()),
        required: true,
        rust_value: if measured {
            summary.rust_wall_seconds_geomean.map(|value| value * 1000.0)
        } else {
            None
        },
        trust_value: if measured {
            summary.trust_wall_seconds_geomean.map(|value| value * 1000.0)
        } else {
            None
        },
        higher_is_better: Some(false),
        min_trust_delta_pct: Some(0.000001),
        max_trust_regression_pct: None,
        status,
        unit: Some("ms_geomean".to_string()),
        weight: 1.0,
        evidence: vec![format!(
            "{}: schema={} compile_profile_schema={} target_arch={} baseline_slot={} trust_slot={} mode={} cache_state={} candidate_pairs={} comparable_pairs={} rust_wall_ms_geomean={} trust_wall_ms_geomean={} rust_cpu_seconds_geomean={} trust_cpu_seconds_geomean={} rust_peak_rss_geomean={} trust_peak_rss_geomean={} blockers={}",
            path.display(),
            PROGRAM_INDEX_REPORT_SCHEMA,
            PROGRAM_INDEX_COMPILE_MEASUREMENT_PROFILE_SCHEMA,
            arch.evidence_token(),
            PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
            PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
            mode.expected_profile_mode(),
            mode.expected_cache_state(),
            summary.candidate_pairs,
            summary.comparable_pairs,
            summary
                .rust_wall_seconds_geomean
                .map(|value| format!("{:.3}", value * 1000.0))
                .unwrap_or_else(|| "n/a".to_string()),
            summary
                .trust_wall_seconds_geomean
                .map(|value| format!("{:.3}", value * 1000.0))
                .unwrap_or_else(|| "n/a".to_string()),
            summary
                .rust_cpu_seconds_geomean
                .map(|value| format!("{value:.6}"))
                .unwrap_or_else(|| "n/a".to_string()),
            summary
                .trust_cpu_seconds_geomean
                .map(|value| format!("{value:.6}"))
                .unwrap_or_else(|| "n/a".to_string()),
            summary
                .rust_peak_rss_geomean
                .map(|value| format!("{value:.0}"))
                .unwrap_or_else(|| "n/a".to_string()),
            summary
                .trust_peak_rss_geomean
                .map(|value| format!("{value:.0}"))
                .unwrap_or_else(|| "n/a".to_string()),
            summary.blockers.len()
        )],
        ai_hint: Some(if measured {
            "Keep compile wall-time, CPU-time, and peak-RSS evidence fresh for the reviewed commit."
                .to_string()
        } else if summary.blockers.is_empty() {
            mode.rerun_hint().to_string()
        } else {
            format!("{}. Blockers: {}", mode.rerun_hint(), summary.blockers.join("; "))
        }),
        owner: None,
        evidence_source: DimensionEvidenceSource::ProgramIndexRuntimeBinaryReport,
    }
}

fn read_product_proof_release_report(path: &Path) -> Result<DimensionInput> {
    let content = read_bounded_utf8_file(path, MAX_RELEASE_TRANSCRIPT_REPORT_BYTES)
        .with_context(|| format!("failed to read {} safely", path.display()))?;
    let report: Value = serde_json::from_str(&content)
        .with_context(|| format!("failed to parse JSON release report {}", path.display()))?;

    let mut blockers = Vec::new();
    if report.get("schema_version").and_then(Value::as_str) != Some(RELEASE_REPORT_SCHEMA) {
        bail!(
            "release report {} has schema_version {:?}, expected {RELEASE_REPORT_SCHEMA}",
            path.display(),
            report.get("schema_version").and_then(Value::as_str)
        );
    }
    if value_at(&report, "profile") != Some("product-proof") {
        blockers.push("release report profile must be product-proof".to_string());
    }
    if value_at(&report, "visibility") != Some("public") {
        blockers.push("release report visibility must be public".to_string());
    }
    if value_at(&report, "evidence_mode") != Some("golden-path") {
        blockers.push("release report evidence_mode must be golden-path".to_string());
    }
    match report.get("release_evidence").and_then(Value::as_object) {
        Some(release_evidence) => {
            if release_evidence.get("claim").and_then(Value::as_str) != Some("golden-path") {
                blockers
                    .push("release report release_evidence.claim must be golden-path".to_string());
            }
            if release_evidence.get("golden_path").and_then(Value::as_bool) != Some(true) {
                blockers
                    .push("release report release_evidence.golden_path must be true".to_string());
            }
        }
        None => blockers.push(
            "release report must include structured release_evidence golden-path semantics"
                .to_string(),
        ),
    }
    if value_at(&report, "status") != Some("pass") {
        blockers.push(format!(
            "release report status must be pass, got {:?}",
            value_at(&report, "status")
        ));
    }
    if value_at(&report, "candidate_command") != Some("targo trust release check") {
        blockers.push("candidate_command must be targo trust release check".to_string());
    }
    match report.get("repo_dirty").and_then(Value::as_bool) {
        Some(false) => {}
        Some(true) => {
            blockers.push("release report repo_dirty must be false for proof evidence".to_string())
        }
        None => blockers
            .push("release report must include repo_dirty=false for proof evidence".to_string()),
    }
    blockers.extend(release_report_dirty_metadata_blockers(&report));
    match report.get("runner") {
        Some(runner) if product_proof_release_runner_is_trust_owned(runner) => {}
        Some(_) => blockers.push(
            "release report runner must declare python_used=false and a Rust-owned targo trust release check entrypoint"
                .to_string(),
        ),
        None => blockers.push("release report must include structured runner identity".to_string()),
    }
    let candidate_commit = match value_at(&report, "candidate_commit") {
        Some(commit) if is_full_git_sha(commit) => Some(commit),
        Some(commit) => {
            blockers.push(format!(
                "release report candidate_commit must be a full git SHA, got `{commit}`"
            ));
            Some(commit)
        }
        None => {
            blockers.push("release report must bind candidate_commit".to_string());
            None
        }
    };
    let mut release_candidate_values = Vec::new();
    collect_product_proof_candidate_commit_values(&report, &mut release_candidate_values);
    if let Some(expected) = candidate_commit {
        for actual in release_candidate_values {
            if actual != expected {
                blockers.push(format!(
                    "release report contains conflicting candidate_commit `{actual}`, expected `{expected}`"
                ));
            }
        }
    }

    let product_proof_gate = report.get("reports").and_then(Value::as_array).and_then(|reports| {
        reports.iter().find(|gate| value_at(gate, "gate") == Some("product-proof-coverage"))
    });
    match product_proof_gate {
        Some(gate) if value_at(gate, "status") == Some("pass") => {}
        Some(gate) => blockers.push(format!(
            "product-proof-coverage gate must pass, got {:?}",
            value_at(gate, "status")
        )),
        None => {
            blockers.push("release report must include product-proof-coverage gate".to_string())
        }
    }

    let binary_decomp_component =
        report.get("product_proof_components").and_then(Value::as_array).and_then(|components| {
            components.iter().find(|component| {
                value_at(component, "component") == Some(PRODUCT_PROOF_BINARY_DECOMP_COMPONENT)
            })
        });
    match binary_decomp_component {
        Some(component) if value_at(component, "status") == Some("accepted") => {
            let required_evidence = component
                .get("required_evidence")
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default();
            for required in COMPILE_BACK_REQUIRED_EVIDENCE {
                if !required_evidence.iter().any(|item| item.as_str() == Some(required)) {
                    blockers.push(format!(
                        "{PRODUCT_PROOF_BINARY_DECOMP_COMPONENT} component required_evidence must include {required}"
                    ));
                }
            }
        }
        Some(component) => blockers.push(format!(
            "{PRODUCT_PROOF_BINARY_DECOMP_COMPONENT} component must be accepted, got {:?}",
            value_at(component, "status")
        )),
        None => blockers.push(format!(
            "release report must include {PRODUCT_PROOF_BINARY_DECOMP_COMPONENT} component"
        )),
    }

    let evidence_refs = product_proof_gate
        .and_then(|gate| gate.get("evidence_refs"))
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let evidence_root = match product_proof_release_repo_root(path, &report) {
        Ok(root) => Some(root),
        Err(error) => {
            blockers
                .push(format!("release report repo_root could not be resolved safely: {error}"));
            None
        }
    };
    let mut compile_back_identities = BTreeMap::new();
    for required in COMPILE_BACK_REQUIRED_EVIDENCE {
        let mut found_required_ref = false;
        for item in &evidence_refs {
            let Some(evidence_ref) = item.as_str() else {
                blockers.push("product-proof-coverage evidence_refs must be strings".to_string());
                continue;
            };
            if !evidence_ref_kind_matches(evidence_ref, required) {
                continue;
            }
            let Some(path_text) = evidence_ref_path(evidence_ref, required) else {
                blockers.push(format!(
                    "product-proof-coverage evidence_refs must include {required}:<path>"
                ));
                continue;
            };
            found_required_ref = true;
            if let Some(evidence_root) = evidence_root.as_deref() {
                validate_compile_back_evidence_ref(
                    evidence_root,
                    required,
                    path_text,
                    candidate_commit,
                    &mut compile_back_identities,
                    &mut blockers,
                );
            }
        }
        if !found_required_ref {
            blockers.push(format!(
                "product-proof-coverage evidence_refs must include {required}:<path>"
            ));
        }
    }

    let status = if blockers.is_empty() {
        DeclaredStatus::Pass
    } else if product_proof_gate.is_none() || binary_decomp_component.is_none() {
        DeclaredStatus::Unknown
    } else {
        DeclaredStatus::Fail
    };
    Ok(DimensionInput {
        id: PRODUCT_PROOF_BINARY_ROUNDTRIP_DIMENSION_ID.to_string(),
        title: "Source-to-binary proof and translation validation".to_string(),
        category: DimensionCategory::Verification,
        metric: Some(MetricKind::PassRate),
        comparison_baseline: Some(
            "rustc codegen plus external disassembly/decompilation tools without proof-grade source binding"
                .to_string(),
        ),
        required: true,
        rust_value: if status == DeclaredStatus::Pass { Some(0.0) } else { None },
        trust_value: if status == DeclaredStatus::Pass { Some(1.0) } else { None },
        higher_is_better: Some(true),
        min_trust_delta_pct: None,
        max_trust_regression_pct: None,
        status: Some(status),
        unit: Some("product_proof_release_report".to_string()),
        weight: 1.0,
        evidence: vec![format!(
            "{}: schema={} profile=product-proof binary_decomp_component={} compile_back_refs={} blockers={}",
            path.display(),
            RELEASE_REPORT_SCHEMA,
            binary_decomp_component.and_then(|component| value_at(component, "status")).unwrap_or("missing"),
            COMPILE_BACK_REQUIRED_EVIDENCE.len(),
            blockers.len()
        )],
        ai_hint: Some(if blockers.is_empty() {
            "Keep the product-proof release report fresh for the reviewed commit.".to_string()
        } else {
            format!(
                "Rerun `targo trust release check --profile product-proof --visibility public --json` with accepted binary/decomp compile-back evidence. Blockers: {}",
                blockers.join("; ")
            )
        }),
        owner: None,
        evidence_source: DimensionEvidenceSource::ProductProofReleaseReport,
    })
}

fn release_report_dirty_metadata_blockers(report: &Value) -> Vec<String> {
    let mut blockers = Vec::new();
    let metadata = report.get("repo_dirty_metadata").unwrap_or(&Value::Null);
    if metadata.get("available").and_then(Value::as_bool) != Some(true) {
        blockers.push("release report must include repo_dirty_metadata.available=true".to_string());
    }
    if metadata.get("dirty").and_then(Value::as_bool) != Some(false) {
        blockers.push("release report must include repo_dirty_metadata.dirty=false".to_string());
    }
    match value_at(metadata, "untracked_files") {
        Some("all") => {}
        Some("included") => blockers.push(
            "release report repo_dirty_metadata.untracked_files must be all, not included"
                .to_string(),
        ),
        _ => blockers.push(
            "release report repo_dirty_metadata must include untracked_files=all".to_string(),
        ),
    }
    if value_at(metadata, "ignore_submodules") != Some("none") {
        blockers.push(
            "release report repo_dirty_metadata must include ignore_submodules=none".to_string(),
        );
    }
    blockers
}

fn product_proof_release_runner_is_trust_owned(runner: &Value) -> bool {
    trust_runner_is_trust_owned(runner, TrustRunnerEntrypoint::ProductProofRelease)
}

fn product_proof_evidence_runner_is_trust_owned(runner: &Value) -> bool {
    runner.get("python_used").and_then(Value::as_bool) == Some(false)
        && !value_declares_python_command_marker(runner)
        && runner_declares_rust_implementation(runner)
        && runner_declares_trust_product_tool(runner)
}

fn runner_declares_trust_product_tool(runner: &Value) -> bool {
    [
        "identity",
        "entrypoint",
        "command",
        "command_line",
        "argv",
        "args",
        "executable",
        "path",
        "binary",
    ]
    .iter()
    .filter_map(|key| runner.get(*key))
    .any(value_declares_trust_product_tool_entrypoint)
}

fn value_declares_trust_product_tool_entrypoint(value: &Value) -> bool {
    let mut tokens = Vec::new();
    collect_runner_command_tokens(value, &mut tokens);
    runner_tokens_declare_trust_product_tool_entrypoint(&tokens)
}

fn runner_tokens_declare_trust_product_tool_entrypoint(tokens: &[String]) -> bool {
    [
        &["targo", "trust", "release", "check"][..],
        &["targo-trust", "trust", "release", "check"],
        &["targo", "trust", "verify-binary"],
        &["targo-trust", "trust", "verify-binary"],
        &["targo", "trust", "decompile"],
        &["targo-trust", "trust", "decompile"],
        &["targo", "trust", "convert"],
        &["targo-trust", "trust", "convert"],
        &["targo", "trust", "lift"],
        &["targo-trust", "trust", "lift"],
    ]
    .into_iter()
    .any(|expected| tokens_contain_sequence(tokens, expected))
        || tokens.iter().any(|token| {
            matches!(
                token.as_str(),
                "trust-decompile"
                    | "trust-lift"
                    | "trust-cg"
                    | "trust-vc"
                    | "trust-wp"
                    | "trust-ir"
            )
        })
}

#[derive(Clone, Copy)]
enum CompileBackEvidenceValueKind {
    Sha256,
    Range,
}

#[derive(Clone, Copy)]
struct CompileBackEvidenceField {
    name: &'static str,
    artifact_path_name: Option<&'static str>,
    value_kind: CompileBackEvidenceValueKind,
}

const COMPILE_BACK_LIFTED_BINARY_TRUST_IR_FIELD: &[CompileBackEvidenceField] =
    &[CompileBackEvidenceField {
        name: "lifted_binary_trust_ir_sha256",
        artifact_path_name: Some("lifted_binary_trust_ir_path"),
        value_kind: CompileBackEvidenceValueKind::Sha256,
    }];
const COMPILE_BACK_RUST_SOURCE_FIELD: &[CompileBackEvidenceField] = &[CompileBackEvidenceField {
    name: "rust_source_sha256",
    artifact_path_name: Some("rust_source_path"),
    value_kind: CompileBackEvidenceValueKind::Sha256,
}];
const COMPILE_BACK_RECONSTRUCTED_TRUST_IR_FIELD: &[CompileBackEvidenceField] =
    &[CompileBackEvidenceField {
        name: "reconstructed_trust_ir_sha256",
        artifact_path_name: Some("reconstructed_trust_ir_path"),
        value_kind: CompileBackEvidenceValueKind::Sha256,
    }];
const COMPILE_BACK_REFINEMENT_ARTIFACT_FIELD: &[CompileBackEvidenceField] =
    &[CompileBackEvidenceField {
        name: "refinement_artifact_sha256",
        artifact_path_name: Some("refinement_artifact_path"),
        value_kind: CompileBackEvidenceValueKind::Sha256,
    }];
const COMPILE_BACK_ROOT_ARTIFACT_FIELD: &[CompileBackEvidenceField] = &[CompileBackEvidenceField {
    name: "root_artifact_sha256",
    artifact_path_name: Some("root_artifact_path"),
    value_kind: CompileBackEvidenceValueKind::Sha256,
}];
const COMPILE_BACK_SELECTED_IMAGE_FIELD: &[CompileBackEvidenceField] =
    &[CompileBackEvidenceField {
        name: "selected_image_sha256",
        artifact_path_name: Some("selected_image_path"),
        value_kind: CompileBackEvidenceValueKind::Sha256,
    }];
const COMPILE_BACK_SELECTED_IMAGE_RANGE_FIELD: &[CompileBackEvidenceField] =
    &[CompileBackEvidenceField {
        name: "selected_image_range",
        artifact_path_name: None,
        value_kind: CompileBackEvidenceValueKind::Range,
    }];
const COMPILE_BACK_ALL_FIELDS: &[CompileBackEvidenceField] = &[
    COMPILE_BACK_LIFTED_BINARY_TRUST_IR_FIELD[0],
    COMPILE_BACK_RUST_SOURCE_FIELD[0],
    COMPILE_BACK_RECONSTRUCTED_TRUST_IR_FIELD[0],
    COMPILE_BACK_REFINEMENT_ARTIFACT_FIELD[0],
    COMPILE_BACK_ROOT_ARTIFACT_FIELD[0],
    COMPILE_BACK_SELECTED_IMAGE_FIELD[0],
    COMPILE_BACK_SELECTED_IMAGE_RANGE_FIELD[0],
];

fn validate_compile_back_evidence_ref(
    evidence_root: &Path,
    required: &str,
    path_text: &str,
    candidate_commit: Option<&str>,
    compile_back_identities: &mut BTreeMap<&'static str, String>,
    blockers: &mut Vec<String>,
) {
    if !is_json_path(Path::new(path_text)) {
        blockers.push(format!("{required} evidence ref {path_text} must point to a JSON artifact"));
        return;
    }
    let evidence_path = match resolve_product_proof_evidence_path(evidence_root, path_text) {
        Ok(path) => path,
        Err(error) => {
            blockers.push(format!(
                "could not resolve {required} evidence artifact `{path_text}` safely: {error}"
            ));
            return;
        }
    };
    let content = match read_bounded_utf8_file(&evidence_path, MAX_RELEASE_TRANSCRIPT_REPORT_BYTES)
    {
        Ok(content) => content,
        Err(err) => {
            blockers.push(format!(
                "could not reopen {required} evidence artifact {} safely: {err}",
                evidence_path.display()
            ));
            return;
        }
    };
    let evidence: Value = match serde_json::from_str(&content) {
        Ok(evidence) => evidence,
        Err(err) => {
            blockers.push(format!(
                "{required} evidence artifact {} is not valid JSON: {err}",
                evidence_path.display()
            ));
            return;
        }
    };
    validate_compile_back_evidence_json(
        required,
        evidence_root,
        &evidence_path,
        &evidence,
        candidate_commit,
        compile_back_identities,
        blockers,
    );
}

fn validate_compile_back_evidence_json(
    required: &str,
    evidence_root: &Path,
    evidence_path: &Path,
    evidence: &Value,
    candidate_commit: Option<&str>,
    compile_back_identities: &mut BTreeMap<&'static str, String>,
    blockers: &mut Vec<String>,
) {
    match value_at(evidence, "schema_version") {
        Some(schema) if schema == PRODUCT_PROOF_EVIDENCE_SCHEMA => {}
        Some(schema) => blockers.push(format!(
            "{required} evidence artifact {} has schema_version `{schema}`, expected `{PRODUCT_PROOF_EVIDENCE_SCHEMA}`",
            evidence_path.display()
        )),
        None => blockers.push(format!(
            "{required} evidence artifact {} must declare schema_version `{PRODUCT_PROOF_EVIDENCE_SCHEMA}`",
            evidence_path.display()
        )),
    }
    if !product_proof_evidence_declares_kind(evidence, required) {
        blockers.push(format!(
            "{required} evidence artifact {} must declare evidence_kind/evidence_kinds `{required}`",
            evidence_path.display()
        ));
    }
    match (candidate_commit, product_proof_declared_candidate_commit(evidence)) {
        (Some(expected), Some(actual)) if expected == actual => {}
        (Some(expected), Some(actual)) => blockers.push(format!(
            "{required} evidence artifact {} binds candidate_commit `{actual}`, expected `{expected}`",
            evidence_path.display()
        )),
        (Some(expected), None) => blockers.push(format!(
            "{required} evidence artifact {} must bind candidate_commit `{expected}`",
            evidence_path.display()
        )),
        (None, _) => {}
    }
    let mut candidate_values = Vec::new();
    collect_product_proof_candidate_commit_values(evidence, &mut candidate_values);
    if let Some(expected) = candidate_commit {
        for actual in candidate_values {
            if actual != expected {
                blockers.push(format!(
                    "{required} evidence artifact {} contains conflicting candidate_commit `{actual}`, expected `{expected}`",
                    evidence_path.display()
                ));
            }
        }
    }
    match evidence.get("runner") {
        Some(runner) if product_proof_evidence_runner_is_trust_owned(runner) => {}
        Some(_) => blockers.push(format!(
            "{required} evidence artifact {} runner must declare python_used=false and Rust-owned Trust product-proof tooling",
            evidence_path.display()
        )),
        None => blockers.push(format!(
            "{required} evidence artifact {} must include structured runner identity",
            evidence_path.display()
        )),
    }
    validate_product_proof_declared_totals(required, evidence_path, evidence, blockers);

    let Some(binding) =
        evidence.get("compile_back_artifact_digest_binding").and_then(Value::as_object)
    else {
        blockers.push(format!(
            "{required} evidence artifact {} must include compile_back_artifact_digest_binding",
            evidence_path.display()
        ));
        return;
    };
    let Some(fields) = compile_back_evidence_fields(required) else {
        blockers.push(format!("{required} is not a supported compile-back evidence kind"));
        return;
    };
    for field in fields {
        let Some(value) = binding.get(field.name) else {
            blockers.push(format!(
                "{required} evidence artifact {} must include compile_back_artifact_digest_binding.{}",
                evidence_path.display(),
                field.name
            ));
            continue;
        };
        let Some(normalized) = normalize_compile_back_evidence_value(value, field.value_kind)
        else {
            blockers.push(format!(
                "{required} evidence artifact {} has invalid compile_back_artifact_digest_binding.{}",
                evidence_path.display(),
                field.name
            ));
            continue;
        };
        match compile_back_identities.get(field.name) {
            Some(previous) if previous != &normalized => blockers.push(format!(
                "{required} evidence artifact {} has compile_back_artifact_digest_binding.{} `{normalized}`, conflicting with prior `{previous}`",
                evidence_path.display(),
                field.name
            )),
            Some(_) => {}
            None => {
                compile_back_identities.insert(field.name, normalized.clone());
            }
        }
        if matches!(field.value_kind, CompileBackEvidenceValueKind::Sha256) {
            validate_compile_back_artifact_hash(
                required,
                evidence_root,
                evidence_path,
                binding,
                field,
                &normalized,
                blockers,
            );
        }
    }
}

fn validate_product_proof_declared_totals(
    required: &str,
    evidence_path: &Path,
    evidence: &Value,
    blockers: &mut Vec<String>,
) {
    let Some(results) = evidence.get("proof_results") else {
        blockers.push(format!(
            "{required} evidence artifact {} must include proof_results with declared totals",
            evidence_path.display()
        ));
        return;
    };
    let proved = results.get("proved").and_then(Value::as_u64);
    let total =
        results.get("total").or_else(|| results.get("total_obligations")).and_then(Value::as_u64);
    match total {
        Some(total) if total > 0 => {}
        Some(_) => blockers.push(format!(
            "{required} evidence artifact {} proof_results.total must be positive",
            evidence_path.display()
        )),
        None => blockers.push(format!(
            "{required} evidence artifact {} proof_results.total must be declared",
            evidence_path.display()
        )),
    }
    match (proved, total) {
        (Some(proved), Some(total)) if proved == total && proved > 0 => {}
        (Some(proved), Some(total)) => blockers.push(format!(
            "{required} evidence artifact {} proof_results must prove all declared totals, got proved={proved} total={total}",
            evidence_path.display()
        )),
        (None, _) => blockers.push(format!(
            "{required} evidence artifact {} proof_results.proved must be declared",
            evidence_path.display()
        )),
        _ => {}
    }
    let has_solver = results.get("by_solver").and_then(Value::as_array).is_some_and(|solvers| {
        !solvers.is_empty() && solvers.iter().all(valid_product_proof_solver_identity_value)
    });
    let has_concrete_binding = product_proof_concrete_binding_satisfied(evidence);
    if !has_product_proof_transcript_hash(evidence) && !(has_solver && has_concrete_binding) {
        blockers.push(format!(
            "{required} evidence artifact {} proof_results must include valid by_solver attribution plus a concrete transcript/artifact binding, or proof_transcript_hash",
            evidence_path.display()
        ));
    }
    if !product_proof_evidence_timestamp_satisfied(evidence) {
        blockers.push(format!(
            "{required} evidence artifact {} must carry generated_at/checked_at provenance",
            evidence_path.display()
        ));
    }
    for counter in product_proof_nonzero_non_proof_counters(results) {
        blockers.push(format!(
            "{required} evidence artifact {} proof_results.{counter} must be zero",
            evidence_path.display()
        ));
    }
}

fn product_proof_nonzero_non_proof_counters(results: &Value) -> Vec<String> {
    [
        "failed",
        "unknown",
        "timed_out",
        "timeout",
        "timeouts",
        "total_timed_out",
        "timeout_results",
        "skipped",
        "unknown_results",
        "total_unknown",
        "skipped_results",
        "total_skipped",
        "runtime_checked",
        "inconclusive",
        "unsupported",
        "errored",
        "errors",
    ]
    .into_iter()
    .filter_map(|key| {
        let value = results.get(key).and_then(Value::as_u64).unwrap_or(0);
        (value > 0).then(|| format!("{key}={value}"))
    })
    .collect()
}

fn valid_product_proof_solver_identity_value(value: &Value) -> bool {
    value.as_str().is_some_and(valid_product_proof_solver_identity)
}

fn valid_product_proof_solver_identity(value: &str) -> bool {
    let trimmed = value.trim();
    !trimmed.is_empty()
        && trimmed == value
        && trimmed.chars().all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_' | '.'))
}

fn product_proof_concrete_binding_satisfied(value: &Value) -> bool {
    has_product_proof_transcript_hash(value)
        || value
            .get("proof_artifact_sha256")
            .and_then(Value::as_str)
            .is_some_and(sha256_value_satisfied)
        || value.get("compile_back_artifact_digest_binding").and_then(Value::as_object).is_some()
        || value.get("tool_identity").is_some()
        || value.get("version_identity").is_some()
        || value.get("binary_identity").is_some()
        || value.get("source_archive_hashes").is_some()
        || value.get("source_archives").is_some()
        || value.get("source_archive").is_some()
        || value.get("component_artifacts").is_some()
        || value.get("component_artifact").is_some()
        || value.get("artifacts").is_some()
        || value.get("artifact").is_some()
}

fn product_proof_evidence_timestamp_satisfied(value: &Value) -> bool {
    ["generated_at", "checked_at", "produced_at", "timestamp"]
        .into_iter()
        .filter_map(|field| value.get(field))
        .any(timestamp_value_satisfied)
        || ["generated_at", "checked_at", "produced_at", "timestamp"]
            .into_iter()
            .filter_map(|field| {
                value.get("provenance").and_then(|provenance| provenance.get(field))
            })
            .any(timestamp_value_satisfied)
        || ["generated_at", "checked_at", "timestamp"]
            .into_iter()
            .filter_map(|field| value.get("runner").and_then(|runner| runner.get(field)))
            .any(timestamp_value_satisfied)
}

fn timestamp_value_satisfied(value: &Value) -> bool {
    match value {
        Value::Number(number) => number.as_u64().is_some_and(|timestamp| timestamp > 0),
        Value::String(text) => {
            let text = text.trim();
            !text.is_empty() && text.bytes().any(|byte| byte.is_ascii_digit())
        }
        _ => false,
    }
}

fn validate_compile_back_artifact_hash(
    required: &str,
    release_report_path: &Path,
    evidence_path: &Path,
    binding: &serde_json::Map<String, Value>,
    field: &CompileBackEvidenceField,
    expected_sha256: &str,
    blockers: &mut Vec<String>,
) {
    let Some(path_field) = field.artifact_path_name else {
        return;
    };
    let Some(path_text) = binding
        .get(path_field)
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|value| !value.is_empty())
    else {
        blockers.push(format!(
            "{required} evidence artifact {} must include compile_back_artifact_digest_binding.{path_field} so {} can be recomputed",
            evidence_path.display(),
            field.name
        ));
        return;
    };
    if !evidence_ref_path_is_safe(path_text) {
        blockers.push(format!(
            "{required} evidence artifact {} has unsafe compile_back_artifact_digest_binding.{path_field} `{path_text}`",
            evidence_path.display()
        ));
        return;
    }
    let artifact_path = match resolve_product_proof_evidence_path(release_report_path, path_text) {
        Ok(path) => path,
        Err(error) => {
            blockers.push(format!(
                "{required} evidence artifact {} could not resolve compile_back_artifact_digest_binding.{path_field} `{path_text}` safely: {error}",
                evidence_path.display()
            ));
            return;
        }
    };
    match file_sha256_hex(&artifact_path) {
        Ok(actual) if actual == expected_sha256 => {}
        Ok(actual) => blockers.push(format!(
            "{required} evidence artifact {} declares {} `{expected_sha256}`, but {} hashes to `{actual}`",
            evidence_path.display(),
            field.name,
            artifact_path.display()
        )),
        Err(error) => blockers.push(format!(
            "{required} evidence artifact {} could not hash compile_back_artifact_digest_binding.{path_field} {}: {error}",
            evidence_path.display(),
            artifact_path.display()
        )),
    }
}

fn compile_back_evidence_fields(required: &str) -> Option<&'static [CompileBackEvidenceField]> {
    match required {
        "compile-back-artifact-digests-bound" => Some(COMPILE_BACK_ALL_FIELDS),
        "compile-back-lifted-binary-trust_ir-sha256" => {
            Some(COMPILE_BACK_LIFTED_BINARY_TRUST_IR_FIELD)
        }
        "compile-back-rust-source-sha256" => Some(COMPILE_BACK_RUST_SOURCE_FIELD),
        "compile-back-reconstructed-trust_ir-sha256" => {
            Some(COMPILE_BACK_RECONSTRUCTED_TRUST_IR_FIELD)
        }
        "compile-back-refinement-artifact-sha256" => Some(COMPILE_BACK_REFINEMENT_ARTIFACT_FIELD),
        "compile-back-root-artifact-sha256" => Some(COMPILE_BACK_ROOT_ARTIFACT_FIELD),
        "compile-back-selected-image-sha256" => Some(COMPILE_BACK_SELECTED_IMAGE_FIELD),
        "compile-back-selected-image-range" => Some(COMPILE_BACK_SELECTED_IMAGE_RANGE_FIELD),
        _ => None,
    }
}

fn normalize_compile_back_evidence_value(
    value: &Value,
    value_kind: CompileBackEvidenceValueKind,
) -> Option<String> {
    match value_kind {
        CompileBackEvidenceValueKind::Sha256 => {
            let value = value.as_str()?.trim();
            let value = value.strip_prefix("sha256:").unwrap_or(value).trim();
            trust_types::digest::is_stable_sha256_hex(value).then(|| value.to_ascii_lowercase())
        }
        CompileBackEvidenceValueKind::Range => match value {
            Value::String(text) => normalize_compile_back_range_text(text),
            Value::Object(map) => {
                let start = map.get("start").and_then(Value::as_u64)?;
                let end = map.get("end").and_then(Value::as_u64)?;
                (end > start).then(|| format!("{start}..{end}"))
            }
            _ => None,
        },
    }
}

fn normalize_compile_back_range_text(value: &str) -> Option<String> {
    let (start, end) = value.trim().split_once("..")?;
    let start = start.parse::<u64>().ok()?;
    let end = end.parse::<u64>().ok()?;
    (end > start).then(|| format!("{start}..{end}"))
}

fn product_proof_release_repo_root(
    release_report_path: &Path,
    report: &Value,
) -> std::io::Result<PathBuf> {
    let root = match value_at(report, "repo_root").map(str::trim).filter(|root| !root.is_empty()) {
        Some(root) if Path::new(root).is_absolute() => PathBuf::from(root),
        Some(root) if evidence_ref_path_is_safe(root) => {
            release_report_path.parent().unwrap_or_else(|| Path::new(".")).join(root)
        }
        Some(root) => {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("relative repo_root `{root}` is not a contained path"),
            ));
        }
        None => release_report_path.parent().unwrap_or_else(|| Path::new(".")).to_path_buf(),
    };
    let metadata = fs::symlink_metadata(&root)?;
    if metadata.file_type().is_symlink() || !metadata.file_type().is_dir() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("{} is not a non-symlink directory", root.display()),
        ));
    }
    Ok(root)
}

fn resolve_product_proof_evidence_path(
    evidence_root: &Path,
    path_text: &str,
) -> std::io::Result<PathBuf> {
    if !evidence_ref_path_is_safe(path_text) {
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("evidence path `{path_text}` is not a contained relative path"),
        ));
    }

    let mut resolved = evidence_root.to_path_buf();
    for component in Path::new(path_text).components() {
        match component {
            Component::CurDir => continue,
            Component::Normal(name) => resolved.push(name),
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    format!("evidence path `{path_text}` escapes its declared root"),
                ));
            }
        }
        match fs::symlink_metadata(&resolved) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    format!("evidence path component {} is a symlink", resolved.display()),
                ));
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    Ok(resolved)
}

fn has_product_proof_transcript_hash(value: &Value) -> bool {
    value.get("proof_transcript_hash").and_then(Value::as_str).is_some_and(sha256_value_satisfied)
}

fn sha256_value_satisfied(value: &str) -> bool {
    normalize_sha256_digest(value).is_some()
}

fn normalize_sha256_digest(value: &str) -> Option<String> {
    let value = value.trim();
    let value = value.strip_prefix("sha256:").unwrap_or(value).trim();
    trust_types::digest::is_stable_sha256_hex(value).then(|| value.to_ascii_lowercase())
}

fn file_sha256_hex(path: &Path) -> std::io::Result<String> {
    let bytes = read_bounded_file(path, MAX_BINARY_ARTIFACT_BYTES)?;
    Ok(trust_types::digest::stable_sha256_hex(&bytes))
}


fn product_proof_evidence_declares_kind(value: &Value, expected: &str) -> bool {
    value_at(value, "evidence_kind") == Some(expected)
        || value
            .get("evidence_kinds")
            .and_then(Value::as_array)
            .is_some_and(|kinds| kinds.iter().any(|kind| kind.as_str() == Some(expected)))
}

fn product_proof_declared_candidate_commit(value: &Value) -> Option<&str> {
    value_at(value, "candidate_commit").or_else(|| {
        value.get("provenance").and_then(|provenance| value_at(provenance, "candidate_commit"))
    })
}

fn collect_product_proof_candidate_commit_values<'a>(value: &'a Value, out: &mut Vec<&'a str>) {
    match value {
        Value::Object(map) => {
            for (key, value) in map {
                if key == "candidate_commit" {
                    if let Some(commit) = value.as_str() {
                        out.push(commit);
                    }
                }
                collect_product_proof_candidate_commit_values(value, out);
            }
        }
        Value::Array(values) => {
            for value in values {
                collect_product_proof_candidate_commit_values(value, out);
            }
        }
        _ => {}
    }
}

fn evidence_ref_kind_matches(value: &str, required: &str) -> bool {
    value == required || value.strip_prefix(required).is_some_and(|rest| rest.starts_with(':'))
}

fn evidence_ref_path<'a>(value: &'a str, required: &str) -> Option<&'a str> {
    let path = value.strip_prefix(required).and_then(|rest| rest.strip_prefix(':'))?.trim();
    evidence_ref_path_is_safe(path).then_some(path)
}

fn evidence_ref_path_is_safe(path: &str) -> bool {
    let path = Path::new(path);
    !path.as_os_str().is_empty()
        && !path.is_absolute()
        && !path.components().any(|component| {
            matches!(component, Component::ParentDir | Component::RootDir | Component::Prefix(_))
        })
}

fn json_string_array_contains(value: Option<&Value>, needle: &str) -> bool {
    value
        .and_then(Value::as_array)
        .is_some_and(|values| values.iter().any(|value| value.as_str() == Some(needle)))
}

fn value_at<'a>(value: &'a Value, key: &str) -> Option<&'a str> {
    value.get(key).and_then(Value::as_str)
}

fn json_u64(value: &Value, key: &str) -> u64 {
    value.get(key).and_then(Value::as_u64).unwrap_or(0)
}

fn is_json_path(path: &Path) -> bool {
    path.extension().and_then(|ext| ext.to_str()).is_some_and(|ext| ext == "json")
}

fn default_launch_dimensions() -> Vec<DimensionInput> {
    vec![
        launch_dimension(LaunchDimension {
            id: "compat.aarch64.toolchain",
            title: "AArch64/Arm64 Rust toolchain compatibility",
            category: DimensionCategory::Compatibility,
            metric: MetricKind::PassRate,
            comparison_baseline: "upstream rustc/rustdoc/cargo/rustfmt/clippy/miri/rust-analyzer on the adopted snapshot",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: None,
            evidence: &[
                "targo trust domination upstream-tests --release",
                "tests/upstream-rust/baseline.toml",
            ],
            ai_hint: "Produce a fresh AArch64 upstream-compat summary with zero divergent, excepted, or unknown rows.",
        }),
        launch_dimension(LaunchDimension {
            id: "compat.x86_64.toolchain",
            title: "x86-64 Rust toolchain compatibility",
            category: DimensionCategory::Compatibility,
            metric: MetricKind::PassRate,
            comparison_baseline: "upstream rustc/rustdoc/cargo/rustfmt/clippy/miri/rust-analyzer on the adopted snapshot",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: None,
            evidence: &[
                "targo trust domination upstream-tests --release",
                "tests/upstream-rust/baseline.toml",
            ],
            ai_hint: "Produce a fresh x86-64 upstream-compat summary with zero divergent, excepted, or unknown rows.",
        }),
        launch_dimension(LaunchDimension {
            id: "compile.aarch64.clean-release",
            title: "AArch64 clean release compile time",
            category: DimensionCategory::Performance,
            metric: MetricKind::LatencyMs,
            comparison_baseline: "rustc clean compile, same source, same target, same optimization profile, no verification step",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: Some(0.000001),
            evidence: &[
                "hyperfine-style clean release compile transcript for rustc vs trustc on AArch64",
            ],
            ai_hint: "Benchmark compile-to-compile only on AArch64 and require Trust to beat Rust on wall time, CPU time, and peak RSS.",
        }),
        launch_dimension(LaunchDimension {
            id: "compile.x86_64.clean-release",
            title: "x86-64 clean release compile time",
            category: DimensionCategory::Performance,
            metric: MetricKind::LatencyMs,
            comparison_baseline: "rustc clean compile, same source, same target, same optimization profile, no verification step",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: Some(0.000001),
            evidence: &[
                "hyperfine-style clean release compile transcript for rustc vs trustc on x86-64",
            ],
            ai_hint: "Benchmark compile-to-compile only on x86-64 and require Trust to beat Rust on wall time, CPU time, and peak RSS.",
        }),
        launch_dimension(LaunchDimension {
            id: "compile.aarch64.incremental-debug",
            title: "AArch64 incremental debug compile time",
            category: DimensionCategory::Performance,
            metric: MetricKind::LatencyMs,
            comparison_baseline: "rustc incremental edit-compile loop, same source and profile, no verification step",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: Some(0.000001),
            evidence: &["incremental edit benchmark transcript for rustc vs trustc on AArch64"],
            ai_hint: "Run repeated edit-compile workloads on AArch64 and require Trust to beat Rust at p50, p95, and max.",
        }),
        launch_dimension(LaunchDimension {
            id: "compile.x86_64.incremental-debug",
            title: "x86-64 incremental debug compile time",
            category: DimensionCategory::Performance,
            metric: MetricKind::LatencyMs,
            comparison_baseline: "rustc incremental edit-compile loop, same source and profile, no verification step",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: Some(0.000001),
            evidence: &["incremental edit benchmark transcript for rustc vs trustc on x86-64"],
            ai_hint: "Run repeated edit-compile workloads on x86-64 and require Trust to beat Rust at p50, p95, and max.",
        }),
        launch_dimension(LaunchDimension {
            id: "runtime.aarch64.geomean",
            title: "AArch64 compiled-program runtime geomean",
            category: DimensionCategory::Performance,
            metric: MetricKind::Throughput,
            comparison_baseline: "programs compiled by rustc with the same sources, target CPU, linker, flags, and profile",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: Some(0.000001),
            evidence: &[
                "criterion/perf-suite runtime transcript for Rust-produced vs Trust-produced binaries on AArch64",
            ],
            ai_hint: "Run like-for-like runtime suites on AArch64 and require every benchmark plus geomean to be faster under Trust.",
        }),
        launch_dimension(LaunchDimension {
            id: "runtime.x86_64.geomean",
            title: "x86-64 compiled-program runtime geomean",
            category: DimensionCategory::Performance,
            metric: MetricKind::Throughput,
            comparison_baseline: "programs compiled by rustc with the same sources, target CPU, linker, flags, and profile",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: Some(0.000001),
            evidence: &[
                "criterion/perf-suite runtime transcript for Rust-produced vs Trust-produced binaries on x86-64",
            ],
            ai_hint: "Run like-for-like runtime suites on x86-64 and require every benchmark plus geomean to be faster under Trust.",
        }),
        launch_dimension(LaunchDimension {
            id: "efficiency.aarch64.binary-size",
            title: "AArch64 generated binary size",
            category: DimensionCategory::Performance,
            metric: MetricKind::BinarySizeBytes,
            comparison_baseline: "rustc-generated binaries with identical source, target, flags, profile, strip/debug settings",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: Some(0.000001),
            evidence: &["size/section-size transcript for rustc vs trustc outputs on AArch64"],
            ai_hint: "Measure text/data/total size for AArch64 outputs and require Trust output to be smaller than Rust output.",
        }),
        launch_dimension(LaunchDimension {
            id: "efficiency.x86_64.binary-size",
            title: "x86-64 generated binary size",
            category: DimensionCategory::Performance,
            metric: MetricKind::BinarySizeBytes,
            comparison_baseline: "rustc-generated binaries with identical source, target, flags, profile, strip/debug settings",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: Some(0.000001),
            evidence: &["size/section-size transcript for rustc vs trustc outputs on x86-64"],
            ai_hint: "Measure text/data/total size for x86-64 outputs and require Trust output to be smaller than Rust output.",
        }),
        launch_dimension(LaunchDimension {
            id: "proof.functional-best-existing-tools",
            title: "Functional proof capability beyond Rust plus existing verifier tools",
            category: DimensionCategory::Verification,
            metric: MetricKind::Score,
            comparison_baseline: "best practical Rust stack using Kani, Creusot, Prusti, Verus, MIRAI, Miri, sanitizers, Z3, and manual specs",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: None,
            evidence: &[
                "corpus report showing obligations Trust proves automatically that the best existing Rust stack cannot prove without materially more annotations or manual proof",
            ],
            ai_hint: "Build a public corpus where Trust proves functional properties that Rust plus existing tools cannot prove under the same annotation/time budget.",
        }),
        launch_dimension(LaunchDimension {
            id: PROOF_UNSAFE_MEMORY_DIMENSION_ID,
            title: "Unsafe-code memory proof coverage",
            category: DimensionCategory::Safety,
            metric: MetricKind::PassRate,
            comparison_baseline: "Rust unsafe review plus Miri/sanitizers/Kani/Creusot-style bounded or annotated checks",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: None,
            evidence: &[
                PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND,
                "--proof-unsafe-memory-report <trust.proof-unsafe-memory-report.v1.json>",
            ],
            ai_hint: "Run targo trust report --unsafe-memory and pass a trust.proof-unsafe-memory-report.v1 wrapper with --proof-unsafe-memory-report.",
        }),
        launch_dimension(LaunchDimension {
            id: "proof.concurrency",
            title: "Concurrency, atomics, and data-race proof coverage",
            category: DimensionCategory::Safety,
            metric: MetricKind::PassRate,
            comparison_baseline: "Rust Send/Sync type checks plus Loom/Miri/sanitizers/manual model checking",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: None,
            evidence: &[
                "concurrency proof transcript for data races, atomics, memory ordering, and happens-before obligations",
            ],
            ai_hint: "Prove or refute real concurrent Rust patterns across AArch64 and x86-64 memory behavior with exact blockers for unsupported semantics.",
        }),
        launch_dimension(LaunchDimension {
            id: "proof.binary-source-roundtrip",
            title: "Source-to-binary proof and translation validation",
            category: DimensionCategory::Verification,
            metric: MetricKind::PassRate,
            comparison_baseline: "rustc codegen plus external disassembly/decompilation tools without proof-grade source binding",
            status: DeclaredStatus::Unknown,
            min_trust_delta_pct: None,
            evidence: &[
                "targo trust verify-binary/decompile/convert proof-grade release transcript",
            ],
            ai_hint: "Produce proof-grade source-to-binary evidence with exact provenance, replay, checked certificates, and target-output validation.",
        }),
        launch_trust_advantage_dimension(LaunchDimension {
            id: "feature.frontdoor-cli",
            title: "First-class Trust verifier front door",
            category: DimensionCategory::Feature,
            metric: MetricKind::Score,
            comparison_baseline: "rustc without built-in proof-report and AI-directive workflow",
            status: DeclaredStatus::Pass,
            min_trust_delta_pct: None,
            evidence: &[
                "targo trust check",
                "targo trust check --format json",
                "targo trust report --unsafe-memory",
                "targo trust doctor",
            ],
            ai_hint: "Keep targo trust check/json, unsafe-memory reporting, and doctor stable as the public front door.",
        }),
        launch_trust_advantage_dimension(LaunchDimension {
            id: "feature.binary-analysis-cli",
            title: "First-class binary proof and decompilation CLI surface",
            category: DimensionCategory::Feature,
            metric: MetricKind::Score,
            comparison_baseline: "rustc plus separate objdump/decompiler/proof tooling with no unified Trust report",
            status: DeclaredStatus::Pass,
            min_trust_delta_pct: None,
            evidence: &[
                "targo trust lift",
                "targo trust verify-binary",
                "targo trust decompile",
                "targo trust convert",
            ],
            ai_hint: "Keep binary commands strict and explicit about proof-grade blockers instead of silently trusting partial output.",
        }),
        launch_trust_advantage_dimension(LaunchDimension {
            id: "feature.launch-gate-cli",
            title: "One-line public domination/readiness gate",
            category: DimensionCategory::AiGuidance,
            metric: MetricKind::Score,
            comparison_baseline: "ad hoc launch scripts and prose-only benchmark claims",
            status: DeclaredStatus::Pass,
            min_trust_delta_pct: None,
            evidence: &["targo trust domination", "targo trust domination --json"],
            ai_hint: "Keep this command as the launch-facing scorecard and AI task generator.",
        }),
    ]
}

struct LaunchDimension<'a> {
    id: &'a str,
    title: &'a str,
    category: DimensionCategory,
    metric: MetricKind,
    comparison_baseline: &'a str,
    status: DeclaredStatus,
    min_trust_delta_pct: Option<f64>,
    evidence: &'a [&'a str],
    ai_hint: &'a str,
}

fn launch_dimension(input: LaunchDimension<'_>) -> DimensionInput {
    DimensionInput {
        id: input.id.to_string(),
        title: input.title.to_string(),
        category: input.category,
        metric: Some(input.metric),
        comparison_baseline: Some(input.comparison_baseline.to_string()),
        required: true,
        rust_value: None,
        trust_value: None,
        higher_is_better: Some(!matches!(
            input.metric,
            MetricKind::LatencyMs | MetricKind::BinarySizeBytes | MetricKind::MemoryBytes
        )),
        min_trust_delta_pct: input.min_trust_delta_pct,
        max_trust_regression_pct: None,
        status: Some(input.status),
        unit: None,
        weight: 1.0,
        evidence: input.evidence.iter().map(|item| item.to_string()).collect(),
        ai_hint: Some(input.ai_hint.to_string()),
        owner: None,
        evidence_source: DimensionEvidenceSource::Manual,
    }
}

fn launch_trust_advantage_dimension(input: LaunchDimension<'_>) -> DimensionInput {
    let mut dimension = launch_dimension(input);
    dimension.rust_value = Some(0.0);
    dimension.trust_value = Some(1.0);
    dimension
}

#[cfg(test)]
fn evaluate_suite(
    suite_id: Option<String>,
    policy: EffectivePolicy,
    dimensions: Vec<DimensionInput>,
    compatibility_summary: Option<CompatSummaryIngestReport>,
) -> RustVsTrustReport {
    evaluate_suite_with_extra_blockers(
        suite_id,
        policy,
        dimensions,
        compatibility_summary,
        Vec::new(),
    )
}

fn evaluate_suite_with_extra_blockers(
    suite_id: Option<String>,
    policy: EffectivePolicy,
    dimensions: Vec<DimensionInput>,
    compatibility_summary: Option<CompatSummaryIngestReport>,
    extra_blockers: Vec<Blocker>,
) -> RustVsTrustReport {
    let mut reports = Vec::new();
    let mut blockers = extra_blockers;

    if dimensions.is_empty() {
        blockers.push(Blocker {
            severity: Severity::P1,
            kind: BlockerKind::NoEvidence,
            dimension_id: None,
            message: "no Rust-vs-Trust dimensions were supplied".to_string(),
            action: "Provide --suite, --compat-summary, or both before making a replacement claim."
                .to_string(),
        });
    }

    for dimension in dimensions {
        let report = evaluate_dimension(&dimension, &policy);
        blockers.extend(report.blockers.iter().cloned());
        reports.push(report);
    }

    let summary = summarize(&reports);

    if policy.require_trust_advantage
        && !reports.is_empty()
        && summary.trust_advantage_dimensions == 0
    {
        blockers.push(Blocker {
            severity: Severity::P2,
            kind: BlockerKind::NoTrustAdvantage,
            dimension_id: None,
            message: "Trust has no evidence-backed dimension where it is better than Rust"
                .to_string(),
            action: "Add and pass a required verification, safety, or productivity dimension where Rust has no equivalent result.".to_string(),
        });
    }

    blockers.sort_by_key(|blocker| blocker.severity);
    let verdict = classify_verdict(&policy, &summary, &blockers);
    let ai_directives = blockers.iter().map(directive_from_blocker).collect();

    RustVsTrustReport {
        schema_version: REPORT_SCHEMA_VERSION,
        suite_id,
        verdict,
        policy,
        evidence_requirements: evidence_requirements(),
        summary,
        compatibility_summary,
        blockers,
        ai_directives,
        dimensions: reports,
    }
}

fn evidence_requirements() -> EvidenceRequirements {
    EvidenceRequirements {
        proof_functional_best_existing_tools: EvidenceRequirement {
            dimension_id: PROOF_FUNCTIONAL_DIMENSION_ID,
            required_flag: PROOF_FUNCTIONAL_REPORT_FLAG,
            required_command: PROOF_FUNCTIONAL_EVIDENCE_COMMAND,
            expected_schema: PROGRAM_INDEX_REPORT_SCHEMA,
            required_suite: PROOF_FUNCTIONAL_SUITE,
            required_slot: PROOF_FUNCTIONAL_SLOT,
            current_json_required: true,
            fail_closed_conditions: vec![
                "missing report",
                "wrong schema",
                "dry-run report",
                "missing proof-design trust-verify rows",
                "program_index_evidence missing or not admissible_for_domination",
                "candidate or non-gating program-index rows selected",
                "summary failed/skipped/planned/excepted rows",
                "zero transport obligations",
                "missing or mismatched transport counter corroboration",
                "unknown or runtime_checked obligations",
                "missing or dirty reviewed-commit provenance",
                "reviewed-commit mismatch with other supplied evidence reports",
                "missing known-good or known-flawed observations",
            ],
        },
        proof_unsafe_memory: UnsafeMemoryEvidenceRequirement {
            dimension_id: PROOF_UNSAFE_MEMORY_DIMENSION_ID,
            required_flag: PROOF_UNSAFE_MEMORY_REPORT_FLAG,
            required_command: PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND,
            expected_schema: PROOF_UNSAFE_MEMORY_REPORT_SCHEMA,
            required_producer_command: PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND,
            required_producer_native: true,
            proof_report_hash_required: true,
            unsupported_must_be_empty: true,
            coverage_counts_required: vec![
                "unsafe_blocks_total",
                "unsafe_blocks_proved",
                "unsafe_operations_total",
                "unsafe_operations_proved",
                "memory_obligations_total",
                "memory_obligations_proved",
            ],
            current_json_required: true,
            fail_closed_conditions: vec![
                "missing report",
                "manual or stale dimension without current unsafe-memory proof report JSON",
                "wrong schema",
                "candidate_commit missing or not a full SHA",
                "repo_dirty not false",
                "producer.native not true",
                "producer.command not exactly targo trust report --unsafe-memory",
                "proof_report_path unsafe, missing, or not hash-bound",
                "proof_report_hash mismatch",
                "coverage totals missing, zero, or not fully proved",
                "unsupported not empty",
                "reviewed-commit mismatch with other supplied evidence reports",
            ],
        },
        proof_concurrency: ProofConcurrencyEvidenceRequirement {
            dimension_id: PROOF_CONCURRENCY_DIMENSION_ID,
            required_flag: PROOF_CONCURRENCY_REPORT_FLAG,
            required_command: PROOF_CONCURRENCY_EVIDENCE_COMMAND,
            expected_schema: PROOF_CONCURRENCY_REPORT_SCHEMA,
            required_obligation_kinds: PROOF_CONCURRENCY_REQUIRED_OBLIGATION_KINDS.to_vec(),
            current_json_required: true,
            fail_closed_conditions: vec![
                "missing report",
                "wrong schema",
                "manual or stale dimension without current proof-concurrency report JSON",
                "unknown JSON fields",
                "missing or dirty reviewed-commit provenance",
                "legacy trust.proof-concurrency.report.v1 presence-only report",
                "artifact-audit or demo/stub schema with proof_authority none",
                "missing trust_kernel_authenticated_replay authority declaration",
                "non-Rust-owned authenticated validator runner or Python-backed runner",
                "stub, demo, fixture, mock, manual, unknown, or URI solver/validator identity",
                "missing authenticated certificate validation, transcript replay, or dispatch authentication",
                "no independently invocable Trust-owned authenticated validator/replayer implementation",
                "empty obligations array",
                "missing data_race_free, atomic_ordering, or happens_before obligation",
                "non-proved, skipped, unsupported, runtime_checked, timed_out, unknown, or failed obligation",
                "manual_pass obligation or summary counter",
                "summary counters not corroborated by obligation rows",
                "missing canonical source/proof/certificate/dispatch SHA-256 binding",
                "source URI, stub label, absolute path, or path traversal",
                "reviewed-commit mismatch with other supplied evidence reports",
            ],
        },
        proof_binary_source_roundtrip: BinarySourceRoundtripEvidenceRequirement {
            dimension_id: PRODUCT_PROOF_BINARY_ROUNDTRIP_DIMENSION_ID,
            required_flag: PRODUCT_PROOF_RELEASE_REPORT_FLAG,
            required_command: "targo trust release check --profile product-proof --visibility public --json",
            expected_schema: RELEASE_REPORT_SCHEMA,
            required_profile: "product-proof",
            required_gate: "product-proof-coverage",
            required_product_proof_component: PRODUCT_PROOF_BINARY_DECOMP_COMPONENT,
            required_product_proof_component_status: "accepted",
            required_compile_back_evidence_kinds: COMPILE_BACK_REQUIRED_EVIDENCE.to_vec(),
            required_compile_back_evidence_declaration: true,
            materialized_artifacts_required: true,
            materialized_artifact_reference_format: "<compile-back-evidence-kind>:<relative-artifact-path>",
            current_json_required: true,
            fail_closed_conditions: vec![
                "missing release report",
                "manual or stale dimension without current product-proof release report JSON",
                "wrong schema",
                "non-product-proof profile",
                "non-pass release report",
                "missing or failing product-proof-coverage gate",
                "missing product-proof component declaration",
                "binary/decomp gates component not accepted",
                "missing compile-back evidence kind declaration",
                "missing materialized compile-back artifact reference",
                "candidate_commit mismatch with other supplied evidence reports",
            ],
        },
    }
}

fn evaluate_dimension(input: &DimensionInput, policy: &EffectivePolicy) -> DimensionReport {
    let mut blockers = Vec::new();
    let evidence_missing = input.required
        && policy.require_evidence_for_required
        && input.evidence.iter().all(|item| item.trim().is_empty());
    let proof_functional_without_program_index_evidence = input.id == PROOF_FUNCTIONAL_DIMENSION_ID
        && input.evidence_source != DimensionEvidenceSource::ProgramIndexProofReport;
    let proof_unsafe_memory_without_report_evidence = input.id == PROOF_UNSAFE_MEMORY_DIMENSION_ID
        && input.evidence_source != DimensionEvidenceSource::ProofUnsafeMemoryReport;
    let proof_concurrency_without_report_evidence = input.id == PROOF_CONCURRENCY_DIMENSION_ID
        && input.evidence_source != DimensionEvidenceSource::ProofConcurrencyReport;
    let product_proof_without_release_report_evidence = input.id
        == PRODUCT_PROOF_BINARY_ROUNDTRIP_DIMENSION_ID
        && input.evidence_source != DimensionEvidenceSource::ProductProofReleaseReport;
    let requires_structured_proof_evidence = proof_functional_without_program_index_evidence
        || proof_unsafe_memory_without_report_evidence
        || proof_concurrency_without_report_evidence
        || product_proof_without_release_report_evidence;

    if evidence_missing {
        blockers.push(Blocker {
            severity: Severity::P1,
            kind: BlockerKind::MissingEvidence,
            dimension_id: Some(input.id.clone()),
            message: format!("required dimension `{}` has no evidence artifact", input.id),
            action: input.ai_hint.clone().unwrap_or_else(|| {
                "Attach the exact command, commit, machine context, and raw result artifact."
                    .to_string()
            }),
        });
    }
    if proof_functional_without_program_index_evidence {
        blockers.push(Blocker {
            severity: Severity::P1,
            kind: BlockerKind::UnknownResult,
            dimension_id: Some(input.id.clone()),
            message: format!(
                "required dimension `{}` needs current program-index proof-design JSON evidence",
                input.id
            ),
            action: format!(
                "Run `{PROOF_FUNCTIONAL_EVIDENCE_COMMAND}` and pass its JSON report with {PROOF_FUNCTIONAL_REPORT_FLAG}."
            ),
        });
    }
    if proof_unsafe_memory_without_report_evidence {
        blockers.push(Blocker {
            severity: Severity::P1,
            kind: BlockerKind::UnknownResult,
            dimension_id: Some(input.id.clone()),
            message: format!(
                "required dimension `{}` needs current unsafe-memory proof report JSON evidence",
                input.id
            ),
            action: format!(
                "Run `{PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND}` and pass its structured wrapper with {PROOF_UNSAFE_MEMORY_REPORT_FLAG}."
            ),
        });
    }
    if proof_concurrency_without_report_evidence {
        blockers.push(Blocker {
            severity: Severity::P1,
            kind: BlockerKind::UnknownResult,
            dimension_id: Some(input.id.clone()),
            message: format!(
                "required dimension `{}` needs current proof-concurrency report JSON evidence",
                input.id
            ),
            action: format!(
                "Run `{PROOF_CONCURRENCY_EVIDENCE_COMMAND}` and pass its JSON report with {PROOF_CONCURRENCY_REPORT_FLAG}."
            ),
        });
    }
    if product_proof_without_release_report_evidence {
        blockers.push(Blocker {
            severity: Severity::P1,
            kind: BlockerKind::UnknownResult,
            dimension_id: Some(input.id.clone()),
            message: format!(
                "required dimension `{}` needs current product-proof release report JSON evidence",
                input.id
            ),
            action: format!(
                "Run `targo trust release check --profile product-proof --visibility public --json` and pass its JSON report with {PRODUCT_PROOF_RELEASE_REPORT_FLAG}."
            ),
        });
    }

    let higher_is_better = input.higher_is_better.unwrap_or(match input.metric {
        Some(MetricKind::LatencyMs | MetricKind::BinarySizeBytes | MetricKind::MemoryBytes) => {
            false
        }
        Some(
            MetricKind::Score | MetricKind::PassRate | MetricKind::Throughput | MetricKind::Count,
        )
        | None => true,
    });

    let mut delta_pct = None;
    let mut trust_is_better = false;
    let mut trust_is_worse = false;
    let mut status = DimensionStatus::Unknown;

    match input.status {
        Some(DeclaredStatus::Pass) => {
            status =
                if evidence_missing { DimensionStatus::Unknown } else { DimensionStatus::Pass };
            if let (Some(rust), Some(trust)) = (input.rust_value, input.trust_value) {
                if rust.is_finite() && trust.is_finite() {
                    let comparison = compare_values(rust, trust, higher_is_better);
                    delta_pct = comparison.delta_pct;
                    trust_is_better = comparison.trust_is_better;
                    trust_is_worse = comparison.trust_is_worse;
                }
            }
        }
        Some(DeclaredStatus::Fail) => {
            status = DimensionStatus::Fail;
            blockers.push(Blocker {
                severity: if input.category == DimensionCategory::Compatibility {
                    Severity::P0
                } else {
                    Severity::P1
                },
                kind: if input.category == DimensionCategory::Compatibility {
                    BlockerKind::CompatibilityNotProven
                } else {
                    BlockerKind::DeclaredFailure
                },
                dimension_id: Some(input.id.clone()),
                message: format!("required dimension `{}` is reported as failed", input.id),
                action: input.ai_hint.clone().unwrap_or_else(|| {
                    "Fix the failing row and rerun the evidence command.".to_string()
                }),
            });
        }
        Some(DeclaredStatus::Unknown) => {
            if !requires_structured_proof_evidence {
                blockers.push(Blocker {
                    severity: Severity::P1,
                    kind: BlockerKind::UnknownResult,
                    dimension_id: Some(input.id.clone()),
                    message: format!("required dimension `{}` is not classified", input.id),
                    action: input.ai_hint.clone().unwrap_or_else(|| {
                        "Run the missing test or add enough instrumentation to classify it."
                            .to_string()
                    }),
                });
            }
        }
        None => match (input.rust_value, input.trust_value) {
            (Some(rust), Some(trust)) if rust.is_finite() && trust.is_finite() => {
                let comparison = compare_values(rust, trust, higher_is_better);
                delta_pct = comparison.delta_pct;
                trust_is_better = comparison.trust_is_better;
                trust_is_worse = comparison.trust_is_worse;

                let allowed_regression = input
                    .max_trust_regression_pct
                    .unwrap_or_else(|| allowed_regression_pct(input.category, policy));
                let required_advantage = input
                    .min_trust_delta_pct
                    .unwrap_or_else(|| required_advantage_pct(input.category, policy));

                if comparison.regression_pct > allowed_regression {
                    status = DimensionStatus::Fail;
                    blockers.push(Blocker {
                        severity: Severity::P0,
                        kind: BlockerKind::Regression,
                        dimension_id: Some(input.id.clone()),
                        message: format!(
                            "Trust regresses `{}` by {:.3}% (allowed {:.3}%)",
                            input.id, comparison.regression_pct, allowed_regression
                        ),
                        action: input.ai_hint.clone().unwrap_or_else(|| {
                            "Remove the regression or change the claim so this metric is not required."
                                .to_string()
                        }),
                    });
                } else if required_advantage > 0.0 && comparison.advantage_pct < required_advantage
                {
                    status = DimensionStatus::Fail;
                    blockers.push(Blocker {
                        severity: Severity::P1,
                        kind: BlockerKind::NoTrustAdvantage,
                        dimension_id: Some(input.id.clone()),
                        message: format!(
                            "Trust advantage for `{}` is {:.3}% but policy requires {:.3}%",
                            input.id, comparison.advantage_pct, required_advantage
                        ),
                        action: input.ai_hint.clone().unwrap_or_else(|| {
                            "Optimize Trust or lower the public claim for this metric.".to_string()
                        }),
                    });
                } else {
                    status = if evidence_missing {
                        DimensionStatus::Unknown
                    } else {
                        DimensionStatus::Pass
                    };
                }
            }
            (Some(rust), Some(trust)) => {
                blockers.push(Blocker {
                    severity: Severity::P1,
                    kind: BlockerKind::InvalidMetric,
                    dimension_id: Some(input.id.clone()),
                    message: format!(
                        "dimension `{}` has non-finite values rust={rust:?} trust={trust:?}",
                        input.id
                    ),
                    action: "Replace NaN or infinite metric values with finite measured values."
                        .to_string(),
                });
            }
            _ => {
                blockers.push(Blocker {
                    severity: Severity::P1,
                    kind: BlockerKind::UnknownResult,
                    dimension_id: Some(input.id.clone()),
                    message: format!(
                        "dimension `{}` needs either status or both rust_value and trust_value",
                        input.id
                    ),
                    action: input.ai_hint.clone().unwrap_or_else(|| {
                        "Record Rust and Trust values for this metric, or import a pass/fail result."
                            .to_string()
                    }),
                });
            }
        },
    }

    if requires_structured_proof_evidence && status == DimensionStatus::Pass {
        status = DimensionStatus::Unknown;
        delta_pct = None;
        trust_is_better = false;
        trust_is_worse = false;
    }

    if input.required
        && policy.require_compatibility_floor
        && input.category == DimensionCategory::Compatibility
        && status != DimensionStatus::Pass
        && !blockers.iter().any(|blocker| blocker.kind == BlockerKind::CompatibilityNotProven)
    {
        blockers.push(Blocker {
            severity: Severity::P0,
            kind: BlockerKind::CompatibilityNotProven,
            dimension_id: Some(input.id.clone()),
            message: format!("Rust compatibility floor is not proven for `{}`", input.id),
            action: input.ai_hint.clone().unwrap_or_else(|| {
                "Make this compatibility row pass without exceptions before claiming replacement."
                    .to_string()
            }),
        });
    }

    if input.required
        && policy.require_no_unknowns
        && status == DimensionStatus::Unknown
        && !blockers.iter().any(|blocker| blocker.kind == BlockerKind::UnknownResult)
    {
        blockers.push(Blocker {
            severity: Severity::P1,
            kind: BlockerKind::UnknownResult,
            dimension_id: Some(input.id.clone()),
            message: format!("required dimension `{}` remains unknown", input.id),
            action: input.ai_hint.clone().unwrap_or_else(|| {
                "Add a deterministic gate that classifies this dimension.".to_string()
            }),
        });
    }

    let recommendation = input.ai_hint.clone().unwrap_or_else(|| match status {
        DimensionStatus::Pass => {
            "Keep this evidence fresh for the exact reviewed commit.".to_string()
        }
        DimensionStatus::Fail => {
            "Fix the failing comparison before making a superiority claim.".to_string()
        }
        DimensionStatus::Unknown => "Add evidence that classifies this comparison.".to_string(),
    });

    DimensionReport {
        id: input.id.clone(),
        title: input.title.clone(),
        category: input.category,
        required: input.required,
        status,
        metric: input.metric,
        comparison_baseline: input.comparison_baseline.clone(),
        unit: input.unit.clone(),
        rust_value: input.rust_value,
        trust_value: input.trust_value,
        delta_pct,
        min_trust_delta_pct: input.min_trust_delta_pct,
        max_trust_regression_pct: input.max_trust_regression_pct,
        trust_is_better,
        trust_is_worse,
        weight: input.weight,
        evidence: input.evidence.clone(),
        blockers,
        owner: input.owner.clone(),
        recommendation,
    }
}

#[derive(Debug, Clone, Copy)]
struct ValueComparison {
    delta_pct: Option<f64>,
    trust_is_better: bool,
    trust_is_worse: bool,
    advantage_pct: f64,
    regression_pct: f64,
}

fn compare_values(rust: f64, trust: f64, higher_is_better: bool) -> ValueComparison {
    let better_delta = if higher_is_better { trust - rust } else { rust - trust };
    let trust_is_better = better_delta > f64::EPSILON;
    let trust_is_worse = better_delta < -f64::EPSILON;
    let denominator = rust.abs();

    let delta_pct = if denominator > f64::EPSILON {
        Some(better_delta / denominator * 100.0)
    } else if trust_is_better {
        Some(100.0)
    } else if trust_is_worse {
        Some(-100.0)
    } else {
        Some(0.0)
    };

    let advantage_pct = delta_pct.unwrap_or(0.0).max(0.0);
    let regression_pct = (-delta_pct.unwrap_or(0.0)).max(0.0);
    ValueComparison { delta_pct, trust_is_better, trust_is_worse, advantage_pct, regression_pct }
}

fn allowed_regression_pct(category: DimensionCategory, policy: &EffectivePolicy) -> f64 {
    if !policy.require_no_regressions {
        return f64::MAX;
    }

    match category {
        DimensionCategory::Performance => policy.max_performance_regression_pct,
        DimensionCategory::Compatibility
        | DimensionCategory::Feature
        | DimensionCategory::Verification
        | DimensionCategory::Safety
        | DimensionCategory::Ergonomics
        | DimensionCategory::Distribution
        | DimensionCategory::AiGuidance
        | DimensionCategory::Other => 0.0,
    }
}

fn required_advantage_pct(category: DimensionCategory, policy: &EffectivePolicy) -> f64 {
    match category {
        DimensionCategory::Performance => policy.min_performance_advantage_pct,
        DimensionCategory::Feature => policy.min_feature_advantage_pct,
        DimensionCategory::Compatibility
        | DimensionCategory::Verification
        | DimensionCategory::Safety
        | DimensionCategory::Ergonomics
        | DimensionCategory::Distribution
        | DimensionCategory::AiGuidance
        | DimensionCategory::Other => 0.0,
    }
}

fn summarize(reports: &[DimensionReport]) -> RustVsTrustSummary {
    let mut summary = RustVsTrustSummary {
        total_dimensions: reports.len(),
        required_dimensions: 0,
        passed: 0,
        failed: 0,
        unknown: 0,
        missing_evidence: 0,
        regressions: 0,
        compatibility_blockers: 0,
        trust_advantage_dimensions: 0,
        rust_relative_index: 0.0,
        trust_relative_index: 0.0,
    };

    for report in reports {
        if report.required {
            summary.required_dimensions += 1;
        }
        match report.status {
            DimensionStatus::Pass => summary.passed += 1,
            DimensionStatus::Fail => summary.failed += 1,
            DimensionStatus::Unknown => summary.unknown += 1,
        }
        if report.trust_is_better {
            summary.trust_advantage_dimensions += 1;
        }
        if report.blockers.iter().any(|blocker| blocker.kind == BlockerKind::MissingEvidence) {
            summary.missing_evidence += 1;
        }
        if report.blockers.iter().any(|blocker| blocker.kind == BlockerKind::Regression) {
            summary.regressions += 1;
        }
        if report.blockers.iter().any(|blocker| blocker.kind == BlockerKind::CompatibilityNotProven)
        {
            summary.compatibility_blockers += 1;
        }

        let weight = report.weight.max(0.0);
        summary.rust_relative_index += weight;
        summary.trust_relative_index += weight * relative_dimension_value(report);
    }

    summary
}

fn relative_dimension_value(report: &DimensionReport) -> f64 {
    match (report.rust_value, report.trust_value) {
        (Some(rust), Some(trust)) => {
            if report.trust_is_better {
                1.0 + report.delta_pct.unwrap_or(0.0).max(0.0) / 100.0
            } else if report.trust_is_worse {
                (1.0 + report.delta_pct.unwrap_or(0.0) / 100.0).max(0.0)
            } else if rust == trust {
                1.0
            } else {
                0.0
            }
        }
        _ => match report.status {
            DimensionStatus::Pass => 1.0,
            DimensionStatus::Fail | DimensionStatus::Unknown => 0.0,
        },
    }
}

fn classify_verdict(
    policy: &EffectivePolicy,
    summary: &RustVsTrustSummary,
    blockers: &[Blocker],
) -> Verdict {
    let has_p0 = blockers.iter().any(|blocker| blocker.severity == Severity::P0);
    if has_p0 || summary.failed > 0 || summary.regressions > 0 {
        return Verdict::NotSuperior;
    }

    if summary.total_dimensions == 0
        || summary.unknown > 0
        || summary.missing_evidence > 0
        || blockers.iter().any(|blocker| blocker.severity == Severity::P1)
    {
        return Verdict::Unproven;
    }

    if policy.require_trust_advantage && summary.trust_advantage_dimensions == 0 {
        return Verdict::NotSuperior;
    }

    Verdict::Superior
}

fn directive_from_blocker(blocker: &Blocker) -> AiDirective {
    AiDirective {
        priority: blocker.severity,
        area: blocker
            .dimension_id
            .clone()
            .unwrap_or_else(|| format!("{:?}", blocker.kind).to_lowercase()),
        reason: blocker.message.clone(),
        action: blocker.action.clone(),
        owner: None,
    }
}

fn render_terminal(report: &RustVsTrustReport) -> String {
    let mut output = String::new();
    output.push_str("\n=== Rust vs Trust Toolchain Test ===\n\n");
    output.push_str(&format!("Verdict: {}\n", report.verdict.label()));
    if let Some(suite_id) = report.suite_id.as_deref() {
        output.push_str(&format!("Suite: {suite_id}\n"));
    }
    output.push_str(&format!(
        "Dimensions: {} total, {} required, {} passed, {} failed, {} unknown\n",
        report.summary.total_dimensions,
        report.summary.required_dimensions,
        report.summary.passed,
        report.summary.failed,
        report.summary.unknown
    ));
    output.push_str(&format!(
        "Review bar: no regressions={}, no unknowns={}, evidence required={}, compatibility floor={}\n",
        report.policy.require_no_regressions,
        report.policy.require_no_unknowns,
        report.policy.require_evidence_for_required,
        report.policy.require_compatibility_floor
    ));
    output.push_str(&format!(
        "Relative index: Rust {:.3}, Trust {:.3}; Trust advantage dimensions: {}\n",
        report.summary.rust_relative_index,
        report.summary.trust_relative_index,
        report.summary.trust_advantage_dimensions
    ));

    if let Some(compat) = &report.compatibility_summary {
        output.push_str(&format!(
            "Compatibility summary: {} rows, {} compatible, {} non-compatible, {} unknown ({})\n",
            compat.rows, compat.compatible, compat.non_compatible, compat.unknown, compat.path
        ));
    }

    if !report.blockers.is_empty() {
        output.push_str("\nBlockers:\n");
        for blocker in &report.blockers {
            let dimension = blocker.dimension_id.as_deref().unwrap_or("global");
            output.push_str(&format!(
                "  [{}] {dimension}: {}\n      action: {}\n",
                blocker.severity.label(),
                blocker.message,
                blocker.action
            ));
        }
    }

    if !report.ai_directives.is_empty() {
        output.push_str("\nAI directives:\n");
        for directive in &report.ai_directives {
            output.push_str(&format!(
                "  [{}] {}: {}\n      {}\n",
                directive.priority.label(),
                directive.area,
                directive.reason,
                directive.action
            ));
        }
    }

    output.push_str("\nDimension rows:\n");
    for row in &report.dimensions {
        let delta =
            row.delta_pct.map(|value| format!("{value:.3}%")).unwrap_or_else(|| "n/a".to_string());
        output.push_str(&format!(
            "  [{:?}] {} ({}) delta={delta} evidence={}\n",
            row.status,
            row.id,
            row.category.label(),
            row.evidence.len()
        ));
    }

    output.push_str("\n====================================\n");
    output
}

fn default_true() -> bool {
    true
}

fn default_weight() -> f64 {
    1.0
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;

    #[test]
    fn canonical_trust_added_gates_have_only_explicit_weaker_diagnostics() {
        for (canonical, diagnostic) in [
            ("installed", "local-stage2-surface-smoke"),
            ("installed-default", "local-stage2-surface-smoke"),
            ("trust-extra", "trust-extra-smoke"),
            ("public-distribution", "public-distribution-cull-smoke"),
            ("prepublish", "prepublish-local-surface-smoke"),
            ("stage0-lineage", "stage0-metadata-coherence-smoke"),
        ] {
            assert_eq!(
                blocked_canonical_diagnostic(canonical).map(|entry| entry.0),
                Some(diagnostic)
            );
            assert!(!crate::trust_added::is_native_mode(canonical));
            assert!(crate::trust_added::is_native_mode(diagnostic));
        }
    }

    static TEMP_ROOT_COUNTER: AtomicU64 = AtomicU64::new(0);

    fn suite_with(dimensions: Vec<DimensionInput>) -> RustVsTrustReport {
        evaluate_suite(
            Some("test".to_string()),
            EffectivePolicy::from_input(&PolicyInput::default()),
            dimensions,
            None,
        )
    }

    fn numeric_dimension(
        id: &str,
        category: DimensionCategory,
        rust_value: f64,
        trust_value: f64,
    ) -> DimensionInput {
        DimensionInput {
            id: id.to_string(),
            title: id.to_string(),
            category,
            metric: Some(MetricKind::Score),
            comparison_baseline: Some("fixture baseline".to_string()),
            required: true,
            rust_value: Some(rust_value),
            trust_value: Some(trust_value),
            higher_is_better: Some(true),
            min_trust_delta_pct: None,
            max_trust_regression_pct: None,
            status: None,
            unit: None,
            weight: 1.0,
            evidence: vec!["fixture evidence".to_string()],
            ai_hint: None,
            owner: None,
            evidence_source: DimensionEvidenceSource::Manual,
        }
    }

    fn temp_repo_root(label: &str) -> PathBuf {
        let counter = TEMP_ROOT_COUNTER.fetch_add(1, Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock should be after UNIX_EPOCH")
            .as_nanos();
        let root = env::temp_dir().join(format!(
            "targo-trust-rust-vs-trust-{label}-{}-{nanos}-{counter}",
            std::process::id(),
        ));
        fs::create_dir_all(&root).expect("temp repo root should be creatable");
        root
    }

    fn touch_file(path: &Path) {
        fs::create_dir_all(path.parent().expect("test file should have parent"))
            .expect("test file parent should be creatable");
        fs::write(path, "").expect("test file should be writable");
    }

    fn touch_executable_file(path: &Path) {
        touch_file(path);
        chmod_executable(path);
    }

    fn chmod_executable(path: &Path) {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            let mut permissions = fs::metadata(path).expect("test file metadata").permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(path, permissions).expect("test file should become executable");
        }
    }

    #[cfg(unix)]
    fn init_git_head(root: &Path) -> String {
        let status = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(["-c", "init.defaultBranch=main", "init", "--quiet"])
            .status()
            .expect("git init should run");
        assert!(status.success(), "git init should succeed");
        let status = Command::new("git")
            .arg("-C")
            .arg(root)
            .args([
                "-c",
                "user.name=Trust Test",
                "-c",
                "user.email=trust@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "--allow-empty",
                "--message",
                "test head",
                "--quiet",
            ])
            .status()
            .expect("git commit should run");
        assert!(status.success(), "git commit should succeed");
        let output = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(["rev-parse", "HEAD"])
            .output()
            .expect("git rev-parse should run");
        assert!(output.status.success(), "git rev-parse should succeed");
        String::from_utf8_lossy(&output.stdout).trim().to_string()
    }

    #[cfg(unix)]
    fn write_fake_stage2_targo(root: &Path, host: &str, trustc_commit: &str) -> PathBuf {
        let bin_dir = root.join("build").join(host).join("stage2").join("bin");
        fs::create_dir_all(&bin_dir).expect("stage2 bin dir should be creatable");
        let targo = bin_dir.join(targo_binary_name());
        fs::write(&targo, "#!/bin/sh\nprintf 'targo test fixture\\n'\n")
            .expect("fake targo should be writable");
        let trustc = bin_dir.join(trustc_binary_name());
        fs::write(
            &trustc,
            format!(
                "#!/bin/sh\nif [ \"${{1:-}}\" = \"-Vv\" ]; then\n  name=$(basename \"$0\")\n  printf '%s 1.96.0-dev\\n' \"$name\"\n  printf 'binary: %s\\n' \"$name\"\n  printf 'commit-hash: {trustc_commit}\\n'\n  exit 0\nfi\nprintf 'trustc 1.96.0-dev\\n'\n"
            ),
        )
        .expect("fake trustc should be writable");
        chmod_executable(&targo);
        chmod_executable(&trustc);
        targo
    }

    fn write_json(path: &Path, value: &Value) {
        fs::write(
            path,
            serde_json::to_string_pretty(value).expect("fixture JSON should serialize"),
        )
        .expect("fixture JSON should be writable");
    }

    fn proof_program_index_report(rows: Vec<Value>, corpus_proof_design: u64) -> Value {
        let good_rows = rows.iter().filter(|row| row["variant"].as_str() == Some("good")).count();
        let flawed_rows =
            rows.iter().filter(|row| row["variant"].as_str() == Some("flawed")).count();
        let proof_design_verifier_evidence = proof_design_verifier_evidence_fixture(&rows);
        let native_obligations = rows
            .iter()
            .map(|row| row["transport"]["obligation_results"].as_u64().unwrap_or(0))
            .sum::<u64>();
        let native_proved = rows
            .iter()
            .map(|row| row["transport"]["proved_results"].as_u64().unwrap_or(0))
            .sum::<u64>();
        let unsupported_frontend_lowering_gate = serde_json::json!({
            "schema": UNSUPPORTED_FRONTEND_LOWERING_GATE_SCHEMA,
            "status": "passed",
            "backward_compatibility": {
                "legacy_gate_preserved": true,
                "legacy_summary_field": "unsupported_mir_gate",
                "legacy_schema": UNSUPPORTED_MIR_GATE_SCHEMA
            },
            "observation_scope": {
                "completeness_claim": true,
                "completeness_claim_scope": "typed_trust_ir_verifier_ingress_only"
            },
            "frontend_transition": {
                "direct_frontend_proof_authority": false,
                "direct_frontend_status": "structural_non_authoritative",
                "producer_authenticated_by_transport": false,
                "mir_compatibility_proof_path_retained": true
            },
            "total_rows": rows.len(),
            "failed": 0,
            "allowed_expected_gap": 0,
            "native_evidence_complete": rows.len(),
            "diagnostic_surface_only": 0,
            "native_evidence": {
                "obligation_results": native_obligations,
                "typed_transport_results": native_obligations,
                "malformed_typed_transport_results": 0,
                "native_trust_ir_results": native_obligations,
                "proof_evidence_results": native_proved,
                "publishable_native_proof_results": native_proved,
                "proved_results": native_proved
            }
        });
        let unsupported_mir_gate = serde_json::json!({
            "schema": UNSUPPORTED_MIR_GATE_SCHEMA,
            "status": "passed"
        });
        serde_json::json!({
            "schema": PROGRAM_INDEX_REPORT_SCHEMA,
            "runner": {
                "implementation": "rust",
                "entrypoint": "targo trust benchmark program-index",
                "python_used": false
            },
            "dry_run": false,
            "repo_head": "0123456789abcdef0123456789abcdef01234567",
            "repo_dirty": false,
            "repo_dirty_metadata": {
                "available": true,
                "dirty": false,
                "porcelain_v1": [],
                "untracked_files": "all",
                "ignore_submodules": "none"
            },
            "corpus": {
                "programs": corpus_proof_design,
                "pairs": 1,
                "variants": {
                    "good": good_rows,
                    "flawed": flawed_rows
                },
                "suites": {
                    "proof-design": corpus_proof_design
                },
                "slots": ["trust-verify"]
            },
            "summary": {
                "total_rows": rows.len(),
                "passed": rows.len(),
                "failed": 0,
                "excepted": 0,
                "skipped": 0,
                "planned": 0,
                "raw_failed_before_exceptions": 0,
                "known_good_pass": {
                    "status": "passed"
                },
                "known_flawed_rejection": {
                    "status": "passed"
                },
                "unsupported_frontend_lowering_gate": unsupported_frontend_lowering_gate,
                "unsupported_mir_gate": unsupported_mir_gate,
                "program_index_evidence": {
                    "selected_candidate_rows": 0,
                    "selected_gating_rows": rows.len(),
                    "admissible_for_domination": true
                },
                "proof_design_verifier_evidence": {
                    "status": proof_design_verifier_evidence["status"],
                    "required": proof_design_verifier_evidence["required"],
                    "admissible_for_domination": proof_design_verifier_evidence["admissible_for_domination"],
                    "selected_programs": proof_design_verifier_evidence["selected_programs"],
                    "verifier_rows": proof_design_verifier_evidence["verifier_rows"],
                    "accepted_rows": proof_design_verifier_evidence["accepted_rows"]
                }
            },
            "program_index_evidence": {
                "model_source": "index.suite_evidence_model",
                "status": "admissible",
                "selected_programs": rows.len(),
                "selected_pairs": 1,
                "selected_candidate_rows": 0,
                "selected_gating_rows": rows.len(),
                "selected_admissible_gating_rows": rows.len(),
                "admissible_for_domination": true,
                "selected_suite_counts": {
                    "proof-design": rows.len()
                },
                "selected_suites": {
                    "proof-design": {
                        "candidate_rows": 0,
                        "gating": true,
                        "candidate_evidence": false,
                        "admissible_for_domination": true,
                        "evidence_class": "admissible_gating"
                    }
                }
            },
            "proof_design_verifier_evidence": proof_design_verifier_evidence,
            "results": rows
        })
    }

    fn proof_design_verifier_evidence_fixture(rows: &[Value]) -> Value {
        let mut verifier_rows = Vec::new();
        let mut transport_sources = Vec::new();
        let mut total_obligations = 0;
        let mut proved_obligations = 0;
        let mut failed_obligations = 0;
        for row in rows {
            let program_id = row["program_id"].as_str().unwrap_or("unknown");
            let stderr_path = format!("logs/trust-verify/{program_id}.stderr.log");
            let transport = row["transport"].clone();
            let total = transport["total"].as_u64().unwrap_or(0);
            let proved = transport["proved"].as_u64().unwrap_or(0);
            let failed = transport["failed"].as_u64().unwrap_or(0);
            total_obligations += total;
            proved_obligations += proved;
            failed_obligations += failed;
            transport_sources.push(serde_json::json!(stderr_path));
            let transport_fixture = serde_json::json!({
                "protocol": "stderr-line-prefix",
                "prefix": "TRUST_JSON:",
                "function_results": 1,
                "crate_summaries": 0,
                "malformed_lines": 0,
                "total": transport["total"],
                "obligation_results": transport["obligation_results"],
                "proved": transport["proved"],
                "proved_results": transport["proved_results"],
                "failed": transport["failed"],
                "failed_results": transport["failed_results"],
                "unknown": transport["unknown"],
                "unknown_results": transport["unknown_results"],
                "runtime_checked": transport["runtime_checked"],
                "runtime_checked_results": transport["runtime_checked_results"],
                "typed_transport_results": transport["typed_transport_results"],
                "malformed_typed_transport_results": transport["malformed_typed_transport_results"],
                "native_trust_ir_results": transport["native_trust_ir_results"],
                "publishable_native_proof_results": transport["publishable_native_proof_results"],
                "counterexamples": if row["variant"].as_str() == Some("flawed") { 1 } else { 0 },
                "counterexample_models": 0,
                "repair_candidates": 0
            });
            let transport_source = serde_json::json!({
                "kind": "stderr_log",
                "stderr_path": stderr_path,
                "protocol": "stderr-line-prefix",
                "prefix": "TRUST_JSON:"
            });
            verifier_rows.push(serde_json::json!({
                "program_id": program_id,
                "pair_id": row["pair_id"],
                "variant": row["variant"],
                "source": row["source"],
                "source_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "slot": "trust-verify",
                "slot_binary": "build/host/stage2/bin/trustc",
                "slot_binary_source": "repo-stage2",
                "expected": row["expected"],
                "observed": row["observed"],
                "outcome": row["outcome"],
                "classification": row["classification"],
                "accepted": true,
                "blockers": [],
                "obligations": row["obligations"],
                "total_obligations": total,
                "proved_obligations": proved,
                "failed_obligations": failed,
                "unknown_obligations": transport["unknown"].as_u64().unwrap_or(0),
                "runtime_checked_obligations": transport["runtime_checked"].as_u64().unwrap_or(0),
                "transport": transport_fixture,
                "transport_source": transport_source,
                "sample_count": 1
            }));
        }
        serde_json::json!({
            "schema": PROOF_DESIGN_VERIFIER_EVIDENCE_SCHEMA,
            "status": if rows.is_empty() { "not_applicable" } else { "passed" },
            "required": !rows.is_empty(),
            "admissible_for_domination": !rows.is_empty(),
            "selected_programs": rows.len(),
            "verifier_slot": "trust-verify",
            "verifier_rows": rows.len(),
            "accepted_rows": rows.len(),
            "good_rows": rows.iter().filter(|row| row["variant"].as_str() == Some("good")).count(),
            "flawed_rows": rows.iter().filter(|row| row["variant"].as_str() == Some("flawed")).count(),
            "total_obligations": total_obligations,
            "proved_obligations": proved_obligations,
            "failed_obligations": failed_obligations,
            "blocked_reasons": [],
            "stage2_binding": {
                "slot": "trust-verify",
                "status": "bound",
                "binary": "build/host/stage2/bin/trustc",
                "binary_report_path": "build/host/stage2/bin/trustc",
                "source": "repo-stage2",
                "canonical_binary": "trustc",
                "resolved_binary_name": "trustc",
                "canonical_entrypoint": true,
                "repo_stage2": true,
                "stage2_roots": ["build/host/stage2"],
                "extra_args": ["-Z", "trust-verify-level=1", "-Z", "trust-verify-output=json"]
            },
            "toolchain_integrity_status": "unchanged",
            "transport_protocol": "stderr-line-prefix",
            "transport_prefix": "TRUST_JSON:",
            "transport_sources": transport_sources,
            "rows": verifier_rows
        })
    }

    fn proof_row(
        program_id: &str,
        variant: &str,
        observed: &str,
        total: u64,
        proved: u64,
        failed: u64,
        unknown: u64,
        runtime_checked: u64,
    ) -> Value {
        serde_json::json!({
            "program_id": program_id,
            "pair_id": "proof_div_zero",
            "variant": variant,
            "suite": "proof-design",
            "source": format!("examples/bench/program_index/cases/{program_id}.rs"),
            "slot": "trust-verify",
            "expected": observed,
            "observed": observed,
            "outcome": "passed",
            "classification": "as-expected",
            "unsupported_frontend_lowering_gate_status": "native_evidence_complete",
            "obligations": ["division_by_zero"],
            "transport": {
                "total": total,
                "proved": proved,
                "failed": failed,
                "unknown": unknown,
                "runtime_checked": runtime_checked,
                "obligation_results": total,
                "proved_results": proved,
                "failed_results": failed,
                "unknown_results": unknown,
                "runtime_checked_results": runtime_checked,
                "typed_transport_results": total,
                "malformed_typed_transport_results": 0,
                "native_trust_ir_results": total,
                "proof_evidence_results": proved,
                "native_evidence_results": total,
                "publishable_native_proof_results": proved
            }
        })
    }

    fn proof_concurrency_report(obligations: Vec<Value>) -> Value {
        let mut proved = 0;
        let mut failed = 0;
        let mut unknown = 0;
        let mut skipped = 0;
        let mut unsupported = 0;
        let mut runtime_checked = 0;
        let mut timed_out = 0;
        let mut manual_pass = 0;
        for obligation in &obligations {
            match obligation["status"].as_str().unwrap_or("<missing>") {
                "proved" => proved += 1,
                "failed" => failed += 1,
                "unknown" => unknown += 1,
                "skipped" => skipped += 1,
                "unsupported" => unsupported += 1,
                "runtime_checked" => runtime_checked += 1,
                "timed_out" => timed_out += 1,
                "manual_pass" => manual_pass += 1,
                _ => {}
            }
        }
        serde_json::json!({
            "schema": PROOF_CONCURRENCY_REPORT_SCHEMA,
            "proof_authority": "trust_kernel_authenticated_replay",
            "proof_pass": true,
            "generated_at": "2026-06-03T00:00:00Z",
            "repo_head": "0123456789abcdef0123456789abcdef01234567",
            "repo_dirty": false,
            "repo_dirty_metadata": {
                "available": true,
                "dirty": false,
                "porcelain_v1": [],
                "untracked_files": "all",
                "ignore_submodules": "none"
            },
            "runner": {
                "implementation": "rust",
                "language": "rust",
                "runtime": "native",
                "entrypoint": "trust-concurrency-validator",
                "command": "trust-concurrency-validator validate-and-replay",
                "argv": ["trust-concurrency-validator", "validate-and-replay"],
                "python_used": false,
                "tool": "trust-concurrency-validator",
                "version": "1.0.0",
                "mode": "authenticated_validation_replay",
                "proof_success_kind": "independently_authenticated_certificate_validation_and_replay"
            },
            "validation": {
                "status": "validated",
                "validator": "trust-concurrency-validator-v1",
                "validator_sha256": "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
                "validation_record_sha256": "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "authenticated": true,
                "artifacts_authenticated": true,
                "certificates_checked": true,
                "transcripts_replayed": true,
                "dispatches_authenticated": true
            },
            "summary": {
                "total_obligations": obligations.len(),
                "proved": proved,
                "failed": failed,
                "unknown": unknown,
                "skipped": skipped,
                "unsupported": unsupported,
                "runtime_checked": runtime_checked,
                "timed_out": timed_out,
                "manual_pass": manual_pass
            },
            "obligations": obligations
        })
    }

    fn proof_concurrency_obligation(id: &str, kind: &str, status: &str) -> Value {
        serde_json::json!({
            "id": id,
            "kind": kind,
            "status": status,
            "source": format!("tests/concurrency/{id}.rs"),
            "source_sha256": "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
            "memory_model": "portable-rust-plus-aarch64-x86_64",
            "proof": {
                "solver": "ay-concurrency",
                "certificate_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "transcript_sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                "dispatch_sha256": "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
                "validation_record_sha256": "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                "certificate_checked": true,
                "transcript_replayed": true,
                "dispatch_authenticated": true
            }
        })
    }

    fn clean_proof_concurrency_report() -> Value {
        proof_concurrency_report(vec![
            proof_concurrency_obligation("race_free_arc_mutex", "data_race_free", "proved"),
            proof_concurrency_obligation("atomic_release_acquire", "atomic_ordering", "proved"),
            proof_concurrency_obligation("channel_happens_before", "happens_before", "proved"),
        ])
    }

    fn read_proof_concurrency_dimension(
        root_name: &str,
        report: &Value,
    ) -> (PathBuf, DimensionInput) {
        let root = temp_repo_root(root_name);
        let path = root.join("proof-concurrency-report.json");
        write_json(&path, report);
        let dimension =
            read_proof_concurrency_report(&path).expect("proof-concurrency report should parse");
        (root, dimension)
    }

    fn runtime_program_index_report(runtime_rows: Vec<Value>, target_arch: Option<&str>) -> Value {
        let baseline_passed = runtime_rows
            .iter()
            .filter(|row| row["slot"] == PROGRAM_INDEX_RUNTIME_BASELINE_SLOT)
            .count();
        let comparison_passed = runtime_rows
            .iter()
            .filter(|row| row["slot"] != PROGRAM_INDEX_RUNTIME_BASELINE_SLOT)
            .count();
        let mut report = serde_json::json!({
            "schema": PROGRAM_INDEX_REPORT_SCHEMA,
            "runner": {
                "implementation": "rust",
                "entrypoint": "targo trust benchmark program-index",
                "python_used": false
            },
            "dry_run": false,
            "repo_head": "0123456789abcdef0123456789abcdef01234567",
            "repo_dirty": false,
            "repo_dirty_metadata": {
                "available": true,
                "dirty": false,
                "porcelain_v1": [],
                "untracked_files": "all",
                "ignore_submodules": "none"
            },
            "upstream_baseline": {
                "schema": "trust.program-index.upstream-baseline-integrity.v1",
                "status": "passed",
                "baseline_slot": PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                "blockers": [],
                "entries": [{
                    "slot": PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                    "status": "passed",
                    "binary": "/opt/upstream-rust/bin/rustc",
                    "source": "explicit",
                    "blockers": [],
                    "version_probe": {
                        "status": "available",
                        "stdout": "rustc 1.95.0 (fake)\nbinary: rustc\ncommit-hash: 59807616e1fa2540724bfbac14d7976d7e4a3860\nhost: x86_64-unknown-linux-gnu\nrelease: 1.95.0\n",
                        "stderr": "",
                        "trust_marker": false
                    },
                    "sysroot_probe": {
                        "status": "available",
                        "stdout": "/opt/upstream-rust/sysroot\n",
                        "stderr": "",
                        "trust_marker": false
                    }
                }]
            },
            "toolchain_integrity": {
                "status": "unchanged",
                "classification": "as-expected",
                "monitored": true
            },
            "stage2_preflight": {
                "schema": "trust.program-index.stage2-preflight.v1",
                "status": "ready",
                "stage2_roots": ["build/host/stage2"]
            },
            "trust_unlock_path": {
                "schema": "trust.program-index.unlock-path.v1",
                "status": "ready_for_trust_compile_evidence",
                "reason": "fixture Trust slot is canonical"
            },
            "slot_bindings": [
                {
                    "slot": PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                    "mode": "compile",
                    "binary": "/opt/upstream-rust/bin/rustc",
                    "source": "explicit"
                },
                {
                    "slot": PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
                    "mode": "compile",
                    "binary": "build/host/stage2/bin/trustc",
                    "source": "explicit"
                }
            ],
            "summary": {
                "total_rows": 0
            },
            "runtime_parity": {
                "schema": PROGRAM_INDEX_RUNTIME_PARITY_SCHEMA,
                "requested": true,
                "enabled": true,
                "status": "passed",
                "baseline_slot": PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                "summary": {
                    "passed": runtime_rows.len(),
                    "failed": 0,
                    "not_applicable": 0,
                    "known_gap": 0,
                    "baseline_passed": baseline_passed,
                    "comparison_passed": comparison_passed,
                    "comparison_failed": 0,
                    "total_rows": runtime_rows.len()
                },
                "rows": runtime_rows
            },
            "results": []
        });
        if let Some(target_arch) = target_arch {
            report["target_arch"] = serde_json::json!(target_arch);
        }
        attach_strict_performance_evidence_fixture(&mut report);
        report
    }

    fn runtime_row(slot: &str, run_seconds: f64, executable_size: u64) -> Value {
        runtime_row_for("runtime_hello.good", slot, run_seconds, executable_size)
    }

    fn runtime_row_for(
        program_id: &str,
        slot: &str,
        run_seconds: f64,
        executable_size: u64,
    ) -> Value {
        let executable_sha256 = if slot == PROGRAM_INDEX_RUNTIME_BASELINE_SLOT {
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
        } else {
            "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
        };
        serde_json::json!({
            "program_id": program_id,
            "pair_id": program_id.trim_end_matches(".good"),
            "variant": "good",
            "suite": "runtime",
            "source": format!("benchmarks/{program_id}.rs"),
            "source_sha256": "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
            "slot": slot,
            "runtime_participant": true,
            "build_status": "compile_pass",
            "run_status": "run_complete",
            "run_exit_code": 0,
            "run_duration_seconds": run_seconds,
            "runtime_classification": "runtime-parity",
            "run_stdout_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "run_stderr_normalized_sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
            "executable_size_bytes": executable_size,
            "executable_sha256": executable_sha256
        })
    }

    fn compile_program_index_report(compile_rows: Vec<Value>, target_arch: &str) -> Value {
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some(target_arch),
        );
        report["summary"]["total_rows"] = serde_json::json!(compile_rows.len());
        report["summary"]["compile_resource_usage"] =
            serde_json::json!(compile_resource_summary_fixture(&compile_rows));
        report["results"] = serde_json::json!(compile_rows);
        if let Some(mode) = program_index_report_compile_modes(&report).first().copied() {
            report["build_profile"] = serde_json::json!(match mode {
                CompileEvidenceMode::CleanRelease => "release",
                CompileEvidenceMode::IncrementalDebug => "debug",
            });
            report["compile_measurement_mode"] = serde_json::json!(mode.expected_profile_mode());
        }
        attach_strict_performance_evidence_fixture(&mut report);
        report
    }

    fn compile_resource_summary_fixture(rows: &[Value]) -> Value {
        let missing_profile_rows = rows
            .iter()
            .filter(|row| row.get("measurement_profile").and_then(Value::as_object).is_none())
            .count();
        let incremental_rows = rows
            .iter()
            .filter(|row| row["measurement_profile"]["incremental"].as_bool() == Some(true))
            .count();
        let non_incremental_rows = rows
            .iter()
            .filter(|row| row["measurement_profile"]["incremental"].as_bool() == Some(false))
            .count();
        let requested_incremental_rows = rows
            .iter()
            .filter(|row| {
                row["measurement_profile"]["requested_incremental"].as_bool() == Some(true)
            })
            .count();
        let measured_incremental_rows = rows
            .iter()
            .filter(|row| row["measurement_profile"]["incremental"].as_bool() == Some(true))
            .filter(|row| row["measurement_profile"]["status"].as_str() == Some("measured"))
            .count();
        let measured_non_incremental_rows = rows
            .iter()
            .filter(|row| row["measurement_profile"]["incremental"].as_bool() == Some(false))
            .filter(|row| row["measurement_profile"]["status"].as_str() == Some("measured"))
            .count();
        serde_json::json!({
            "rows_with_peak_rss": rows.iter().filter(|row| row["peak_rss_bytes"].as_i64().is_some()).count(),
            "timed_out": rows.iter().filter(|row| row["timed_out"].as_bool() == Some(true)).count(),
            "measurement_profiles": {
                "schema": PROGRAM_INDEX_COMPILE_MEASUREMENT_PROFILE_SCHEMA,
                "missing_profile_rows": missing_profile_rows,
                "incremental_rows": incremental_rows,
                "non_incremental_rows": non_incremental_rows,
                "requested_incremental_rows": requested_incremental_rows,
                "measured_incremental_rows": measured_incremental_rows,
                "measured_non_incremental_rows": measured_non_incremental_rows
            }
        })
    }

    fn compile_row(
        slot: &str,
        mode: CompileEvidenceMode,
        duration_seconds: f64,
        user_cpu_seconds: f64,
        system_cpu_seconds: f64,
        peak_rss_bytes: i64,
    ) -> Value {
        let requested_incremental = mode == CompileEvidenceMode::IncrementalDebug;
        let cache_state = if requested_incremental { "warm_incremental" } else { "cold_artifact" };
        serde_json::json!({
            "program_id": "compile_hello.good",
            "pair_id": "compile_hello",
            "variant": "good",
            "suite": "compile-perf",
            "source": "benchmarks/compile_hello.good.rs",
            "source_sha256": "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
            "slot": slot,
            "slot_mode": "compile",
            "expected": "compile_pass",
            "observed": "compile_pass",
            "outcome": "passed",
            "timed_out": false,
            "duration_seconds": duration_seconds,
            "peak_rss_bytes": peak_rss_bytes,
            "resource_usage": {
                "source": PROGRAM_INDEX_COMPILE_RESOURCE_USAGE_SOURCE,
                "elapsed_seconds": duration_seconds,
                "user_cpu_seconds": user_cpu_seconds,
                "system_cpu_seconds": system_cpu_seconds,
                "peak_rss_bytes": peak_rss_bytes,
                "peak_rss_raw": peak_rss_bytes,
                "peak_rss_raw_unit": "bytes"
            },
            "measurement_profile": {
                "schema": PROGRAM_INDEX_COMPILE_MEASUREMENT_PROFILE_SCHEMA,
                "mode": mode.expected_profile_mode(),
                "phase": "compile_artifact",
                "status": "measured",
                "cache_state": cache_state,
                "requested_incremental": requested_incremental,
                "incremental": requested_incremental,
                "warmup_required": requested_incremental,
                "warmup_valid": requested_incremental,
                "timing_field": "duration_seconds",
                "runtime_measurements_separate": true
            }
        })
    }

    fn attach_strict_performance_evidence_fixture(report: &mut Value) {
        let evidence = strict_performance_evidence_fixture(report);
        report["summary"]["strict_superiority_performance_evidence"] =
            strict_performance_evidence_summary_fixture(&evidence);
        report["strict_superiority_performance_evidence"] = evidence;
    }

    fn strict_performance_evidence_fixture(report: &Value) -> Value {
        let target_arch = value_at(report, "target_arch").unwrap_or("x86_64");
        let target_triple =
            value_at(report, "target_triple").or_else(|| value_at(report, "target_arch"));
        let lanes = serde_json::json!({
            "clean_release_compile": strict_compile_lane_fixture(
                report,
                CompileEvidenceMode::CleanRelease,
                "clean_release_compile",
                "Clean release compile duration evidence from cold artifact compiles",
                target_arch,
                target_triple,
            ),
            "incremental_debug_compile": strict_compile_lane_fixture(
                report,
                CompileEvidenceMode::IncrementalDebug,
                "incremental_debug_compile",
                "Warm incremental debug compile duration evidence",
                target_arch,
                target_triple,
            ),
            "runtime_geomean": strict_runtime_lane_fixture(
                report,
                "runtime_geomean",
                "Linked release runtime geomean evidence",
                "run_duration_seconds",
                target_arch,
                target_triple,
            ),
            "binary_size": strict_runtime_lane_fixture(
                report,
                "binary_size",
                "Linked release executable size evidence",
                "executable_size_bytes",
                target_arch,
                target_triple,
            ),
        });
        let measured_lanes = lanes
            .as_object()
            .expect("strict lanes object")
            .values()
            .filter(|lane| value_at(lane, "status") == Some("measured"))
            .count();
        let blocked_lanes = lanes.as_object().expect("strict lanes object").len() - measured_lanes;
        let status = if blocked_lanes == 0 {
            "complete"
        } else if measured_lanes > 0 {
            "partial"
        } else {
            "blocked"
        };
        serde_json::json!({
            "schema": STRICT_SUPERIORITY_PERFORMANCE_SCHEMA,
            "status": status,
            "admissible_for_domination": status == "complete",
            "measured_lanes": measured_lanes,
            "blocked_lanes": blocked_lanes,
            "blocked_reasons": [],
            "target_arch": target_arch,
            "target_triple": target_triple,
            "host": {
                "arch": target_arch,
                "triple": target_triple,
            },
            "host_arch": target_arch,
            "host_triple": target_triple,
            "repetitions": 1,
            "runtime_repetitions": 1,
            "build_profile": value_at(report, "build_profile").unwrap_or("release"),
            "compile_measurement_mode": value_at(report, "compile_measurement_mode")
                .unwrap_or("cold-artifact"),
            "dry_run": report.get("dry_run").and_then(Value::as_bool).unwrap_or(false),
            "candidate_rejection": {
                "schema": "trust.program-index.evidence-policy.v1",
                "rejected": false,
                "status": "admissible",
                "selected_candidate_rows": 0,
                "selected_gating_rows": 1,
                "selected_admissible_gating_rows": 1,
                "admissible_for_domination": true,
                "blocked_gating_suites": [],
                "reason": "no selected candidate rows were present in the performance source data"
            },
            "baseline_slot": PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
            "trust_slots": [PROGRAM_INDEX_RUNTIME_TRUST_SLOT],
            "lanes": lanes,
        })
    }

    fn strict_performance_evidence_summary_fixture(evidence: &Value) -> Value {
        serde_json::json!({
            "schema": STRICT_SUPERIORITY_PERFORMANCE_SCHEMA,
            "status": evidence["status"],
            "admissible_for_domination": evidence["admissible_for_domination"],
            "measured_lanes": evidence["measured_lanes"],
            "blocked_lanes": evidence["blocked_lanes"],
            "blocked_reasons": evidence["blocked_reasons"],
            "target_arch": evidence["target_arch"],
            "target_triple": evidence["target_triple"],
            "host_arch": evidence["host_arch"],
            "host_triple": evidence["host_triple"],
            "repetitions": evidence["repetitions"],
            "runtime_repetitions": evidence["runtime_repetitions"],
            "build_profile": evidence["build_profile"],
            "compile_measurement_mode": evidence["compile_measurement_mode"],
            "dry_run": evidence["dry_run"],
            "candidate_rejected": evidence["candidate_rejection"]["rejected"],
            "lane_statuses": evidence["lanes"]
                .as_object()
                .map(|lanes| {
                    lanes
                        .iter()
                        .map(|(lane, evidence)| (lane.clone(), evidence["status"].clone()))
                        .collect::<serde_json::Map<String, Value>>()
                })
                .unwrap_or_default(),
        })
    }

    fn strict_compile_lane_fixture(
        report: &Value,
        mode: CompileEvidenceMode,
        lane_id: &str,
        description: &str,
        target_arch: &str,
        target_triple: Option<&str>,
    ) -> Value {
        let rows = report["results"].as_array().cloned().unwrap_or_default();
        let rust = strict_compile_slot_fixture(&rows, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, mode);
        let trust = strict_compile_slot_fixture(&rows, PROGRAM_INDEX_RUNTIME_TRUST_SLOT, mode);
        strict_lane_fixture(
            lane_id,
            description,
            mode.required_build_profile_fixture(),
            Some(mode.expected_profile_mode()),
            "duration_seconds",
            target_arch,
            target_triple,
            rust,
            trust,
        )
    }

    fn strict_runtime_lane_fixture(
        report: &Value,
        lane_id: &str,
        description: &str,
        metric: &str,
        target_arch: &str,
        target_triple: Option<&str>,
    ) -> Value {
        let rows = report["runtime_parity"]["rows"].as_array().cloned().unwrap_or_default();
        let rust = strict_runtime_slot_fixture(&rows, PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, metric);
        let trust = strict_runtime_slot_fixture(&rows, PROGRAM_INDEX_RUNTIME_TRUST_SLOT, metric);
        strict_lane_fixture(
            lane_id,
            description,
            "release",
            None,
            metric,
            target_arch,
            target_triple,
            rust,
            trust,
        )
    }

    fn strict_lane_fixture(
        lane_id: &str,
        description: &str,
        required_build_profile: &str,
        required_compile_measurement_mode: Option<&str>,
        metric: &str,
        target_arch: &str,
        target_triple: Option<&str>,
        rust: Value,
        trust_slot: Value,
    ) -> Value {
        let rust_value = positive_number_value(&rust["value"]);
        let trust_value = positive_number_value(&trust_slot["value"]);
        let measured = rust_value.is_some() && trust_value.is_some();
        let status = if measured { "measured" } else { "blocked" };
        let blocked_reasons = if measured {
            Vec::<Value>::new()
        } else {
            vec![serde_json::json!("fixture lane has no measured baseline/Trust values")]
        };
        let comparisons = match (rust_value, trust_value) {
            (Some(rust_value), Some(trust_value)) => vec![serde_json::json!({
                "trust_slot": PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
                "metric": metric,
                "rust_value": rust["value"],
                "trust_value": trust_slot["value"],
                "ratio_vs_rust": trust_value / rust_value,
                "trust_at_most_rust": trust_value <= rust_value,
                "trust_strictly_better": trust_value < rust_value,
                "comparison_policy": "lower_is_better",
            })],
            _ => Vec::new(),
        };
        serde_json::json!({
            "schema": STRICT_SUPERIORITY_PERFORMANCE_SCHEMA,
            "lane": lane_id,
            "description": description,
            "status": status,
            "admissible_for_domination": measured,
            "blocked_reasons": blocked_reasons,
            "metric": metric,
            "lower_is_better": true,
            "required_build_profile": required_build_profile,
            "required_compile_measurement_mode": required_compile_measurement_mode,
            "actual_build_profile": required_build_profile,
            "actual_compile_measurement_mode": required_compile_measurement_mode
                .unwrap_or("cold-artifact"),
            "target_arch": target_arch,
            "target_triple": target_triple,
            "host_arch": target_arch,
            "host_triple": target_triple,
            "repetitions": 1,
            "runtime_repetitions": 1,
            "rust": rust,
            "trust": {
                PROGRAM_INDEX_RUNTIME_TRUST_SLOT: trust_slot,
            },
            "comparisons": comparisons,
        })
    }

    fn strict_compile_slot_fixture(rows: &[Value], slot: &str, mode: CompileEvidenceMode) -> Value {
        let values = rows
            .iter()
            .filter(|row| value_at(row, "slot") == Some(slot))
            .filter(|row| {
                row["measurement_profile"]["mode"].as_str() == Some(mode.expected_profile_mode())
            })
            .filter_map(|row| positive_f64_at(row, "duration_seconds"))
            .collect::<Vec<_>>();
        strict_slot_fixture(slot, &values, "geomean_seconds")
    }

    fn strict_runtime_slot_fixture(rows: &[Value], slot: &str, metric: &str) -> Value {
        let values = rows
            .iter()
            .filter(|row| value_at(row, "slot") == Some(slot))
            .filter_map(|row| positive_number_value(&row[metric]))
            .collect::<Vec<_>>();
        strict_slot_fixture(
            slot,
            &values,
            if metric.ends_with("size_bytes") { "geomean_size_bytes" } else { "geomean_seconds" },
        )
    }

    fn strict_slot_fixture(slot: &str, values: &[f64], value_kind: &str) -> Value {
        let value = geometric_mean(values).map(|value| {
            if value_kind == "geomean_size_bytes" {
                serde_json::json!(value.round() as u64)
            } else {
                serde_json::json!(value)
            }
        });
        serde_json::json!({
            "slot": slot,
            "value": value.unwrap_or(Value::Null),
            "value_kind": value_kind,
            "rows": values.len(),
            "sample_count": values.len(),
        })
    }

    trait CompileEvidenceModeFixtureExt {
        fn required_build_profile_fixture(self) -> &'static str;
    }

    impl CompileEvidenceModeFixtureExt for CompileEvidenceMode {
        fn required_build_profile_fixture(self) -> &'static str {
            match self {
                CompileEvidenceMode::CleanRelease => "release",
                CompileEvidenceMode::IncrementalDebug => "debug",
            }
        }
    }

    fn clean_compile_program_index_report() -> Value {
        compile_program_index_report(
            vec![
                compile_row(
                    PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                    CompileEvidenceMode::CleanRelease,
                    2.0,
                    1.2,
                    0.3,
                    2_000_000,
                ),
                compile_row(
                    PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
                    CompileEvidenceMode::CleanRelease,
                    1.0,
                    0.7,
                    0.2,
                    1_000_000,
                ),
            ],
            "x86_64-unknown-linux-gnu",
        )
    }

    fn read_x86_clean_compile_dimension(
        root_name: &str,
        report: &Value,
    ) -> (PathBuf, DimensionInput) {
        let root = temp_repo_root(root_name);
        let path = root.join("program-index-report.json");
        write_json(&path, report);

        let dimension = read_program_index_runtime_binary_report(&path)
            .expect("compile report should parse")
            .into_iter()
            .find(|dimension| dimension.id == "compile.x86_64.clean-release")
            .expect("x86 clean compile dimension");
        (root, dimension)
    }

    fn assert_dimension_hint_contains(dimension: &DimensionInput, needles: &[&str]) {
        let hint = dimension.ai_hint.as_deref().expect("dimension ai_hint");
        for needle in needles {
            assert!(hint.contains(needle), "hint missing {needle:?}: {hint}");
        }
    }

    fn compatibility_summary_report_with_runner(runner: Value) -> Value {
        serde_json::json!({
            "schema_version": UPSTREAM_COMPAT_SUMMARY_SCHEMA_VERSION,
            "baseline_id": "baseline.cli",
            "generated_on": "2026-04-26",
            "run_id": "ci-42",
            "repo_head": "0123456789abcdef0123456789abcdef01234567",
            "repo_dirty": false,
            "upstream_revision": "rust-lang/rust:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "runner": runner,
            "totals": {
                "total": 1,
                "compatible": 1,
                "divergent": 0,
                "excepted": 0,
                "fixed_upstream": 0,
                "unknown": 0
            },
            "results": [{
                "baseline_entry_id": "toolchain.rustc",
                "outcome": "compatible",
                "observed": "upstream UI suite passed"
            }]
        })
    }

    fn rust_upstream_compat_runner() -> Value {
        serde_json::json!({
            "implementation": "rust",
            "entrypoint": "targo trust domination upstream-tests",
            "argv": [
                "targo",
                "trust",
                "domination",
                "upstream-tests",
                "--release",
                "--proof-mode",
                "full",
                "--execute",
                "--summary-out",
                "reports/upstream-rust/summary.json"
            ],
            "release_evidence_contract": {
                "entrypoint": "targo trust domination upstream-tests",
                "release": true,
                "execute": true,
                "proof_mode": "full",
                "summary_out": "reports/upstream-rust/summary.json",
                "requires_release": true,
                "requires_execute": true,
                "requires_proof_mode": "full",
                "requires_summary_out": true,
                "satisfied": true
            },
            "python_used": false,
            "tool": "trust-upstream-compat"
        })
    }

    fn rust_vs_trust_args_with_compat_summaries(compat_summary: Vec<PathBuf>) -> RustVsTrustArgs {
        RustVsTrustArgs {
            format: OutputFormat::Json,
            suite: None,
            compat_summary,
            proof_program_index_report: None,
            proof_unsafe_memory_report: None,
            proof_concurrency_report: None,
            program_index_benchmark_report: Vec::new(),
            product_proof_release_report: None,
            out: None,
            write_template: None,
            allow_missing_evidence: false,
            allow_exceptions: false,
            min_performance_advantage_pct: None,
        }
    }

    fn write_compat_summary_fixture(root: &Path, name: &str, target_arch: Option<&str>) -> PathBuf {
        let path = root.join(name);
        let mut summary = compatibility_summary_report_with_runner(rust_upstream_compat_runner());
        if let Some(target_arch) = target_arch {
            summary["target_arch"] = serde_json::json!(target_arch);
        }
        write_json(&path, &summary);
        path
    }

    #[test]
    fn domination_rejects_evidence_reports_from_different_commits() {
        let root = temp_repo_root("domination-mismatched-evidence-commits");
        let compat_path = root.join("compat-summary.json");
        let release_path = root.join("product-proof-release.json");

        let mut summary = compatibility_summary_report_with_runner(rust_upstream_compat_runner());
        summary["repo_head"] = serde_json::json!("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
        write_json(&compat_path, &summary);

        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        write_json(&release_path, &product_proof_release_report(evidence_refs));

        let report = build_report(&RustVsTrustArgs {
            format: OutputFormat::Json,
            suite: None,
            compat_summary: vec![compat_path],
            proof_program_index_report: None,
            proof_unsafe_memory_report: None,
            proof_concurrency_report: None,
            program_index_benchmark_report: Vec::new(),
            product_proof_release_report: Some(release_path),
            out: None,
            write_template: None,
            allow_missing_evidence: false,
            allow_exceptions: false,
            min_performance_advantage_pct: None,
        })
        .expect("valid evidence artifacts should build a domination report");

        let blocker = report
            .blockers
            .iter()
            .find(|blocker| blocker.kind == BlockerKind::InconsistentEvidence)
            .expect("mismatched evidence commits should become a global blocker");
        assert!(blocker.action.contains("compat-summary"));
        assert!(blocker.action.contains("product-proof-release-report"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn domination_accepts_multiple_arch_compatibility_summaries() {
        let root = temp_repo_root("domination-multiple-compat-summaries");
        let aarch64_path = root.join("compat-aarch64.json");
        let x86_path = root.join("compat-x86.json");

        let mut aarch64 = compatibility_summary_report_with_runner(rust_upstream_compat_runner());
        aarch64["target_arch"] = serde_json::json!("AArch64");
        write_json(&aarch64_path, &aarch64);
        let mut x86 = compatibility_summary_report_with_runner(rust_upstream_compat_runner());
        x86["target_arch"] = serde_json::json!("x86_64");
        write_json(&x86_path, &x86);

        let report =
            build_report(&rust_vs_trust_args_with_compat_summaries(vec![aarch64_path, x86_path]))
                .expect("multiple compatibility reports should build a domination report");

        let compatibility_summary =
            report.compatibility_summary.as_ref().expect("aggregate compatibility summary");
        assert_eq!(compatibility_summary.compatible, 2);
        assert!(!report.blockers.iter().any(|blocker| {
            blocker.kind == BlockerKind::CompatibilityNotProven
                && blocker.message.contains("release-grade upstream compatibility")
        }));
        assert!(report.dimensions.iter().any(|dimension| {
            dimension.id == "compat.aarch64.toolchain" && dimension.status == DimensionStatus::Pass
        }));
        assert!(report.dimensions.iter().any(|dimension| {
            dimension.id == "compat.x86_64.toolchain" && dimension.status == DimensionStatus::Pass
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn domination_rejects_missing_arch_compatibility_summary_coverage() {
        let root = temp_repo_root("domination-missing-compat-arch-summary");
        let x86_path = write_compat_summary_fixture(&root, "compat-x86.json", Some("x86_64"));

        let report = build_report(&rust_vs_trust_args_with_compat_summaries(vec![x86_path]))
            .expect("single compatibility report should build with coverage blockers");

        let blocker = report
            .blockers
            .iter()
            .find(|blocker| {
                blocker.dimension_id.as_deref() == Some("compat.aarch64.toolchain")
                    && blocker.message.contains("missing")
                    && blocker.message.contains("target_arch")
            })
            .expect("missing AArch64 summary should block release-grade compatibility");
        assert_eq!(blocker.kind, BlockerKind::CompatibilityNotProven);
        assert_eq!(blocker.severity, Severity::P0);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn domination_rejects_duplicate_arch_compatibility_summary_coverage() {
        let root = temp_repo_root("domination-duplicate-compat-arch-summary");
        let aarch64_path =
            write_compat_summary_fixture(&root, "compat-aarch64.json", Some("aarch64"));
        let x86_path = write_compat_summary_fixture(&root, "compat-x86.json", Some("x86_64"));
        let duplicate_x86_path =
            write_compat_summary_fixture(&root, "compat-x86-duplicate.json", Some("x86_64"));

        let report = build_report(&rust_vs_trust_args_with_compat_summaries(vec![
            aarch64_path,
            x86_path,
            duplicate_x86_path,
        ]))
        .expect("duplicate compatibility reports should build with coverage blockers");

        let blocker = report
            .blockers
            .iter()
            .find(|blocker| {
                blocker.dimension_id.as_deref() == Some("compat.x86_64.toolchain")
                    && blocker.message.contains("duplicate")
                    && blocker.message.contains("target_arch")
            })
            .expect("duplicate x86_64 summary should block release-grade compatibility");
        assert_eq!(blocker.kind, BlockerKind::CompatibilityNotProven);
        assert_eq!(blocker.severity, Severity::P0);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn domination_rejects_legacy_compatibility_summary_without_target_arch_coverage() {
        let root = temp_repo_root("domination-legacy-compat-summary-target-arch");
        let legacy_path = root.join("compat-legacy-x86.json");
        let mut legacy = compatibility_summary_report_with_runner(rust_upstream_compat_runner());
        legacy["baseline_id"] = serde_json::json!("baseline.x86_64-linux");
        legacy["run_id"] = serde_json::json!("x86_64-ci-42");
        write_json(&legacy_path, &legacy);
        let aarch64_path =
            write_compat_summary_fixture(&root, "compat-aarch64.json", Some("AArch64"));

        let report = build_report(&rust_vs_trust_args_with_compat_summaries(vec![
            legacy_path,
            aarch64_path,
        ]))
        .expect("legacy compatibility report should build with coverage blockers");

        assert!(report.blockers.iter().any(|blocker| {
            blocker.kind == BlockerKind::CompatibilityNotProven
                && blocker.dimension_id.is_none()
                && blocker.message.contains("must declare explicit target_arch")
        }));
        let x86_dimension = report
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "compat.x86_64.toolchain")
            .expect("default x86 compatibility dimension");
        assert_eq!(x86_dimension.status, DimensionStatus::Unknown);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn domination_rejects_ambiguous_compatibility_summary_target_arch_coverage() {
        let root = temp_repo_root("domination-ambiguous-compat-arch-summary");
        let ambiguous_path = write_compat_summary_fixture(
            &root,
            "compat-ambiguous.json",
            Some("x86_64-and-aarch64"),
        );
        let aarch64_path =
            write_compat_summary_fixture(&root, "compat-aarch64.json", Some("aarch64"));
        let x86_path = write_compat_summary_fixture(&root, "compat-x86.json", Some("x86_64"));

        let report = build_report(&rust_vs_trust_args_with_compat_summaries(vec![
            ambiguous_path,
            aarch64_path,
            x86_path,
        ]))
        .expect("ambiguous compatibility report should build with coverage blockers");

        assert!(report.blockers.iter().any(|blocker| {
            blocker.kind == BlockerKind::CompatibilityNotProven
                && blocker.dimension_id.is_none()
                && blocker.message.contains("unsupported or ambiguous target_arch")
        }));

        let _ = fs::remove_dir_all(root);
    }

    fn product_proof_release_report(evidence_refs: Vec<String>) -> Value {
        serde_json::json!({
            "schema_version": RELEASE_REPORT_SCHEMA,
            "generated_at": 1,
            "profile": "product-proof",
            "visibility": "public",
            "evidence_mode": "golden-path",
            "release_evidence": {
                "claim": "golden-path",
                "golden_path": true,
                "reason": "public product-proof release check output is eligible to carry golden-path release evidence"
            },
            "status": "pass",
            "exit_code_kind": "success",
            "candidate_commit": "0123456789abcdef0123456789abcdef01234567",
            "repo_dirty": false,
            "repo_dirty_metadata": {
                "available": true,
                "dirty": false,
                "porcelain_v1": [],
                "untracked_files": "all",
                "ignore_submodules": "none"
            },
            "runner_kind": "stage2",
            "candidate_command": "targo trust release check",
            "candidate_command_version": 1,
            "runner": {
                "implementation": "rust",
                "entrypoint": "targo trust release check",
                "python_used": false,
                "tool": "targo-trust"
            },
            "reports": [{
                "gate": "product-proof-coverage",
                "status": "pass",
                "release_critical": true,
                "evidence_refs": evidence_refs,
                "findings": []
            }],
            "product_proof_components": [{
                "component": PRODUCT_PROOF_BINARY_DECOMP_COMPONENT,
                "status": "accepted",
                "required_evidence": COMPILE_BACK_REQUIRED_EVIDENCE
            }]
        })
    }

    fn product_proof_release_report_with_required_evidence(
        evidence_refs: Vec<String>,
        required_evidence: Vec<&str>,
    ) -> Value {
        let mut report = product_proof_release_report(evidence_refs);
        report["product_proof_components"][0]["required_evidence"] =
            serde_json::json!(required_evidence);
        report
    }

    fn assert_product_proof_release_report_fails_with_hint(
        root: &Path,
        label: &str,
        report: Value,
        expected_hint: &[&str],
    ) {
        let path = root.join(format!("{label}.json"));
        write_json(&path, &report);

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        let hint = dimension.ai_hint.as_deref().expect("failures should explain blockers");
        for expected in expected_hint {
            assert!(hint.contains(expected), "hint should contain `{expected}`: {hint}");
        }
    }

    fn product_proof_compile_back_evidence(root: &Path, required: &str) -> Value {
        let digest = materialize_compile_back_artifact(root);
        serde_json::json!({
            "schema_version": PRODUCT_PROOF_EVIDENCE_SCHEMA,
            "evidence_kind": required,
            "generated_at": 1,
            "candidate_commit": "0123456789abcdef0123456789abcdef01234567",
            "runner": {
                "implementation": "rust",
                "entrypoint": "targo trust release check",
                "python_used": false,
                "tool": "targo-trust"
            },
            "proof_results": {
                "proved": 1,
                "total": 1,
                "failed": 0,
                "unknown": 0,
                "by_solver": ["focused-product-proof-test"]
            },
            "compile_back_artifact_digest_binding": compile_back_digest_binding(
                &digest,
                "0..16",
            )
        })
    }

    fn compile_back_digest_binding(digest: &str, selected_image_range: &str) -> Value {
        let artifact_path = compile_back_artifact_path_text();
        serde_json::json!({
            "lifted_binary_trust_ir_sha256": digest,
            "lifted_binary_trust_ir_path": artifact_path,
            "rust_source_sha256": digest,
            "rust_source_path": artifact_path,
            "reconstructed_trust_ir_sha256": digest,
            "reconstructed_trust_ir_path": artifact_path,
            "refinement_artifact_sha256": digest,
            "refinement_artifact_path": artifact_path,
            "root_artifact_sha256": digest,
            "root_artifact_path": artifact_path,
            "selected_image_sha256": digest,
            "selected_image_path": artifact_path,
            "selected_image_range": selected_image_range,
        })
    }

    fn compile_back_artifact_path_text() -> &'static str {
        "release/evidence/artifacts/compile-back-material.bin"
    }

    fn materialize_compile_back_artifact(root: &Path) -> String {
        let artifact_path = root.join(compile_back_artifact_path_text());
        fs::create_dir_all(artifact_path.parent().expect("artifact parent"))
            .expect("compile-back artifact dir");
        fs::write(&artifact_path, b"materialized compile-back artifact fixture\n")
            .expect("write compile-back artifact fixture");
        file_sha256_hex(&artifact_path).expect("hash compile-back artifact fixture")
    }

    fn compile_back_evidence_path_text(required: &str) -> String {
        format!("release/evidence/{required}.json")
    }

    fn write_product_proof_compile_back_evidence(root: &Path) -> Vec<String> {
        fs::create_dir_all(root.join("release/evidence")).expect("evidence dir should be created");
        COMPILE_BACK_REQUIRED_EVIDENCE
            .iter()
            .map(|required| {
                let path_text = compile_back_evidence_path_text(required);
                write_json(
                    &root.join(&path_text),
                    &product_proof_compile_back_evidence(root, required),
                );
                format!("{required}:{path_text}")
            })
            .collect()
    }

    fn proof_unsafe_memory_proof_report_path_text() -> &'static str {
        "proof/full-verifier-report.json"
    }

    fn materialize_proof_unsafe_memory_proof_report(root: &Path) -> String {
        let proof_report_path = root.join(proof_unsafe_memory_proof_report_path_text());
        fs::create_dir_all(proof_report_path.parent().expect("proof report parent"))
            .expect("proof report dir");
        write_json(
            &proof_report_path,
            &serde_json::json!({
                "schema": "trust.full-verifier-report.fixture.v1",
                "status": "pass",
                "unsafe_memory": {
                    "memory_obligations_proved": 3
                }
            }),
        );
        file_sha256_hex(&proof_report_path).expect("hash unsafe-memory proof report")
    }

    fn proof_unsafe_memory_report(root: &Path) -> Value {
        let proof_report_hash = materialize_proof_unsafe_memory_proof_report(root);
        serde_json::json!({
            "schema": PROOF_UNSAFE_MEMORY_REPORT_SCHEMA,
            "candidate_commit": "0123456789abcdef0123456789abcdef01234567",
            "repo_dirty": false,
            "producer": {
                "command": PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND,
                "native": true
            },
            "proof_report_path": proof_unsafe_memory_proof_report_path_text(),
            "proof_report_hash": format!("sha256:{proof_report_hash}"),
            "coverage": {
                "unsafe_blocks_total": 1,
                "unsafe_blocks_proved": 1,
                "unsafe_operations_total": 2,
                "unsafe_operations_proved": 2,
                "memory_obligations_total": 3,
                "memory_obligations_proved": 3
            },
            "unsupported": []
        })
    }

    #[test]
    fn proof_unsafe_memory_report_ingests_clean_report() {
        let root = temp_repo_root("proof-unsafe-memory-clean");
        let path = root.join("unsafe-memory.json");
        write_json(&path, &proof_unsafe_memory_report(&root));

        let dimension =
            read_proof_unsafe_memory_report(&path).expect("unsafe-memory report should ingest");

        assert_eq!(dimension.status, Some(DeclaredStatus::Pass));
        assert_eq!(dimension.id, PROOF_UNSAFE_MEMORY_DIMENSION_ID);
        assert_eq!(dimension.trust_value, Some(3.0));
        assert_eq!(dimension.evidence_source, DimensionEvidenceSource::ProofUnsafeMemoryReport);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_unsafe_memory_manual_pass_spoof_is_rejected() {
        let mut dimension = numeric_dimension(
            PROOF_UNSAFE_MEMORY_DIMENSION_ID,
            DimensionCategory::Safety,
            0.0,
            1.0,
        );
        dimension.status = Some(DeclaredStatus::Pass);
        dimension.evidence = vec!["manual pass: unsafe memory proved".to_string()];

        let report = suite_with(vec![dimension]);
        let row = report
            .dimensions
            .iter()
            .find(|row| row.id == PROOF_UNSAFE_MEMORY_DIMENSION_ID)
            .expect("unsafe-memory dimension");

        assert_eq!(row.status, DimensionStatus::Unknown);
        assert!(row.blockers.iter().any(|blocker| {
            blocker.kind == BlockerKind::UnknownResult
                && blocker.action.contains(PROOF_UNSAFE_MEMORY_REPORT_FLAG)
        }));
    }

    #[test]
    fn proof_unsafe_memory_report_rejects_dirty_repo() {
        let root = temp_repo_root("proof-unsafe-memory-dirty");
        let path = root.join("unsafe-memory.json");
        let mut report = proof_unsafe_memory_report(&root);
        report["repo_dirty"] = serde_json::json!(true);
        write_json(&path, &report);

        let dimension = read_proof_unsafe_memory_report(&path).expect("dirty report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(
            dimension
                .ai_hint
                .as_deref()
                .is_some_and(|hint| { hint.contains("repo_dirty must be false") })
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_unsafe_memory_report_rejects_non_native_producer() {
        let root = temp_repo_root("proof-unsafe-memory-producer");
        let path = root.join("unsafe-memory.json");
        let mut report = proof_unsafe_memory_report(&root);
        report["producer"]["native"] = serde_json::json!(false);
        report["producer"]["command"] = serde_json::json!("python scripts/report.py");
        write_json(&path, &report);

        let dimension =
            read_proof_unsafe_memory_report(&path).expect("bad producer report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("producer.native must be true")
                && hint.contains("producer.command must be")
                && hint.contains("Python")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_unsafe_memory_report_rejects_bad_hash_and_unsupported() {
        let root = temp_repo_root("proof-unsafe-memory-bad");
        let path = root.join("unsafe-memory.json");
        let mut report = proof_unsafe_memory_report(&root);
        report["proof_report_hash"] = serde_json::json!(
            "sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
        );
        report["unsupported"] = serde_json::json!(["raw-pointer-provenance-gap"]);
        write_json(&path, &report);

        let dimension = read_proof_unsafe_memory_report(&path).expect("bad report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("proof_report_hash") && hint.contains("unsupported must be empty")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn superior_requires_compatibility_and_advantage() {
        let report = suite_with(vec![
            numeric_dimension("compat.rustc", DimensionCategory::Compatibility, 1.0, 1.0),
            numeric_dimension("proof.overflow", DimensionCategory::Verification, 0.0, 1.0),
        ]);

        assert_eq!(report.verdict, Verdict::Superior);
        assert_eq!(report.summary.trust_advantage_dimensions, 1);
    }

    #[test]
    fn status_pass_dimension_with_values_counts_trust_advantage() {
        let mut dimension =
            numeric_dimension("feature.frontdoor-cli", DimensionCategory::Feature, 0.0, 1.0);
        dimension.status = Some(DeclaredStatus::Pass);

        let report = suite_with(vec![dimension]);

        assert_eq!(report.summary.passed, 1);
        assert_eq!(report.summary.trust_advantage_dimensions, 1);
        assert!(report.dimensions[0].trust_is_better);
    }

    #[test]
    fn proof_functional_manual_pass_is_forced_unknown_without_program_index_json() {
        let mut dimension = numeric_dimension(
            PROOF_FUNCTIONAL_DIMENSION_ID,
            DimensionCategory::Verification,
            0.0,
            1.0,
        );
        dimension.status = Some(DeclaredStatus::Pass);

        let report = suite_with(vec![dimension]);

        assert_eq!(report.dimensions[0].status, DimensionStatus::Unknown);
        assert!(!report.dimensions[0].trust_is_better);
        assert!(report.blockers.iter().any(|blocker| {
            blocker.dimension_id.as_deref() == Some(PROOF_FUNCTIONAL_DIMENSION_ID)
                && blocker.kind == BlockerKind::UnknownResult
                && blocker.action.contains("--proof-program-index-report")
        }));
    }

    #[test]
    fn proof_concurrency_manual_pass_is_forced_unknown_without_structured_report_json() {
        let mut dimension =
            numeric_dimension(PROOF_CONCURRENCY_DIMENSION_ID, DimensionCategory::Safety, 0.0, 1.0);
        dimension.status = Some(DeclaredStatus::Pass);

        let report = suite_with(vec![dimension]);

        assert_eq!(report.dimensions[0].status, DimensionStatus::Unknown);
        assert!(!report.dimensions[0].trust_is_better);
        assert!(report.blockers.iter().any(|blocker| {
            blocker.dimension_id.as_deref() == Some(PROOF_CONCURRENCY_DIMENSION_ID)
                && blocker.kind == BlockerKind::UnknownResult
                && blocker.action.contains(PROOF_CONCURRENCY_REPORT_FLAG)
        }));
    }

    #[test]
    fn proof_concurrency_authenticated_shape_still_fails_without_real_validator() {
        let root = temp_repo_root("proof-concurrency-clean");
        let path = root.join("proof-concurrency-report.json");
        write_json(&path, &clean_proof_concurrency_report());

        let dimension =
            read_proof_concurrency_report(&path).expect("clean concurrency report should ingest");
        assert_eq!(dimension.id, PROOF_CONCURRENCY_DIMENSION_ID);
        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert_eq!(dimension.rust_value, None);
        assert_eq!(dimension.trust_value, None);
        assert!(dimension.evidence.iter().any(|item| {
            item.contains(PROOF_CONCURRENCY_REPORT_SCHEMA)
                && item.contains("obligations=3")
                && item.contains("proved=3")
        }));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("no Trust-owned authenticated concurrency validator/replayer")
        }));

        let report = suite_with(vec![dimension]);
        assert_eq!(report.dimensions[0].status, DimensionStatus::Fail);
        assert!(!report.dimensions[0].trust_is_better);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_concurrency_rejects_legacy_presence_only_and_nonproof_audit_schemas() {
        for (label, schema) in [
            ("legacy", "trust.proof-concurrency.report.v1"),
            ("artifact", "trust.proof-concurrency.artifact-audit.v1"),
            ("demo", "trust.proof-concurrency.demo-audit.v1"),
        ] {
            let root = temp_repo_root(&format!("proof-concurrency-{label}-schema"));
            let path = root.join("proof-concurrency-report.json");
            let mut report = clean_proof_concurrency_report();
            report["schema"] = serde_json::json!(schema);
            write_json(&path, &report);

            let error = read_proof_concurrency_report(&path)
                .expect_err("non-proof concurrency schemas must be rejected before scoring");
            let message = error.to_string();
            assert!(message.contains("non-admissible schema"), "{message}");
            assert!(message.contains("no proof authority"), "{message}");
            let _ = fs::remove_dir_all(root);
        }
    }

    #[test]
    fn proof_concurrency_rejects_stub_solver_uri_source_and_fabricated_validation() {
        for noncanonical in ["proofs/./race.rs", "proofs//race.rs", "../proofs/race.rs"] {
            assert!(
                !canonical_proof_concurrency_source(noncanonical),
                "non-canonical source alias must be rejected: {noncanonical}"
            );
        }

        let mut report = clean_proof_concurrency_report();
        report["validation"]["validator"] = serde_json::json!("stub://validator");
        report["obligations"][0]["source"] = serde_json::json!("stub://source/race-free");
        report["obligations"][0]["proof"]["solver"] =
            serde_json::json!("trust-concurrency-stub-v1");
        report["obligations"][0]["proof"]["certificate_checked"] = serde_json::json!(false);

        let (root, dimension) =
            read_proof_concurrency_dimension("proof-concurrency-fabricated-authority", &report);
        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("non-stub local validator identity")
                && hint.contains("not a URI or stub label")
                && hint.contains("non-stub local solver identity")
                && hint.contains("certificate_checked must be true")
                && hint.contains("no Trust-owned authenticated concurrency validator/replayer")
        }));
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_concurrency_rejects_wrong_schema_report() {
        let root = temp_repo_root("proof-concurrency-wrong-schema");
        let path = root.join("proof-concurrency-report.json");
        let mut report = clean_proof_concurrency_report();
        report["schema"] = serde_json::json!("trust.proof-concurrency.report.v0");
        write_json(&path, &report);

        let error = read_proof_concurrency_report(&path)
            .expect_err("wrong proof-concurrency schema should fail closed");
        let message = error.to_string();
        assert!(message.contains("schema"));
        assert!(message.contains(PROOF_CONCURRENCY_REPORT_SCHEMA));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_concurrency_rejects_malformed_report_unknown_fields() {
        let root = temp_repo_root("proof-concurrency-unknown-field");
        let path = root.join("proof-concurrency-report.json");
        let mut report = clean_proof_concurrency_report();
        report["manual_status"] = serde_json::json!("pass");
        write_json(&path, &report);

        let error = read_proof_concurrency_report(&path)
            .expect_err("unknown proof-concurrency schema fields should fail closed");
        assert!(error.to_string().contains("failed to parse JSON proof-concurrency report"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_concurrency_rejects_dirty_report_provenance() {
        let mut report = clean_proof_concurrency_report();
        report["repo_dirty"] = serde_json::json!(true);

        let (root, dimension) =
            read_proof_concurrency_dimension("proof-concurrency-dirty", &report);

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("repo_dirty must be false")
                && hint.contains(PROOF_CONCURRENCY_REPORT_FLAG)
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_concurrency_rejects_skipped_obligation_report() {
        let report = proof_concurrency_report(vec![
            proof_concurrency_obligation("race_free_arc_mutex", "data_race_free", "proved"),
            proof_concurrency_obligation("atomic_release_acquire", "atomic_ordering", "skipped"),
            proof_concurrency_obligation("channel_happens_before", "happens_before", "proved"),
        ]);

        let (root, dimension) =
            read_proof_concurrency_dimension("proof-concurrency-skipped", &report);

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("status must be proved, got skipped")
                && hint.contains("summary.skipped must be 0")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_concurrency_rejects_unknown_obligation_report() {
        let report = proof_concurrency_report(vec![
            proof_concurrency_obligation("race_free_arc_mutex", "data_race_free", "proved"),
            proof_concurrency_obligation("atomic_release_acquire", "atomic_ordering", "proved"),
            proof_concurrency_obligation("channel_happens_before", "happens_before", "unknown"),
        ]);

        let (root, dimension) =
            read_proof_concurrency_dimension("proof-concurrency-unknown", &report);

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("status must be proved, got unknown")
                && hint.contains("summary.unknown must be 0")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_concurrency_rejects_manual_pass_obligation_report() {
        let report = proof_concurrency_report(vec![
            proof_concurrency_obligation("race_free_arc_mutex", "data_race_free", "proved"),
            proof_concurrency_obligation(
                "atomic_release_acquire",
                "atomic_ordering",
                "manual_pass",
            ),
            proof_concurrency_obligation("channel_happens_before", "happens_before", "proved"),
        ]);

        let (root, dimension) =
            read_proof_concurrency_dimension("proof-concurrency-manual-pass", &report);

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("manual_pass is not admissible proof evidence")
                && hint.contains("summary.manual_pass must be 0")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_manual_pass_is_forced_unknown_without_release_report_json() {
        let mut dimension = numeric_dimension(
            PRODUCT_PROOF_BINARY_ROUNDTRIP_DIMENSION_ID,
            DimensionCategory::Verification,
            0.0,
            1.0,
        );
        dimension.status = Some(DeclaredStatus::Pass);

        let report = suite_with(vec![dimension]);

        assert_eq!(report.dimensions[0].status, DimensionStatus::Unknown);
        assert!(!report.dimensions[0].trust_is_better);
        assert!(report.blockers.iter().any(|blocker| {
            blocker.dimension_id.as_deref() == Some(PRODUCT_PROOF_BINARY_ROUNDTRIP_DIMENSION_ID)
                && blocker.kind == BlockerKind::UnknownResult
                && blocker.action.contains(PRODUCT_PROOF_RELEASE_REPORT_FLAG)
        }));
    }

    #[test]
    fn product_proof_commit_mismatch_blocks_golden_path_evidence() {
        let root = temp_repo_root("product-proof-stale-commit-binding");
        let proof_path = root.join("proof-program-index-report.json");
        let product_path = root.join("product-proof-release-report.json");
        let blockers = evidence_commit_consistency_blockers(&[
            EvidenceCommitBinding::new(
                "proof-program-index-report",
                &proof_path,
                "0123456789abcdef0123456789abcdef01234567".to_string(),
            ),
            EvidenceCommitBinding::new(
                "product-proof-release-report",
                &product_path,
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string(),
            ),
        ]);

        assert_eq!(blockers.len(), 1);
        assert_eq!(blockers[0].kind, BlockerKind::InconsistentEvidence);
        assert_eq!(blockers[0].severity, Severity::P0);
        assert_eq!(blockers[0].dimension_id, None);
        assert!(blockers[0].message.contains("different reviewed commits"));
        assert!(blockers[0].action.contains("proof-program-index-report"));
        assert!(blockers[0].action.contains("product-proof-release-report"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn default_report_metadata_names_proof_functional_program_index_requirement() {
        let report = evaluate_suite(
            Some("default".to_string()),
            EffectivePolicy::from_input(&PolicyInput::default()),
            default_launch_dimensions(),
            None,
        );
        let value = serde_json::to_value(&report).expect("report should serialize");
        let requirement = &value["evidence_requirements"]["proof_functional_best_existing_tools"];

        assert_eq!(requirement["dimension_id"], PROOF_FUNCTIONAL_DIMENSION_ID);
        assert_eq!(requirement["required_flag"], PROOF_FUNCTIONAL_REPORT_FLAG);
        assert_eq!(requirement["required_command"], PROOF_FUNCTIONAL_EVIDENCE_COMMAND);
        assert_eq!(requirement["expected_schema"], PROGRAM_INDEX_REPORT_SCHEMA);
        assert_eq!(requirement["required_suite"], PROOF_FUNCTIONAL_SUITE);
        assert_eq!(requirement["required_slot"], PROOF_FUNCTIONAL_SLOT);
        assert_eq!(requirement["current_json_required"], true);
        assert!(
            requirement["fail_closed_conditions"]
                .as_array()
                .expect("fail-closed conditions")
                .iter()
                .any(|condition| condition == "zero transport obligations")
        );
        assert!(
            requirement["fail_closed_conditions"]
                .as_array()
                .expect("fail-closed conditions")
                .iter()
                .any(|condition| condition
                    == "missing or mismatched transport counter corroboration")
        );
        assert!(
            requirement["fail_closed_conditions"]
                .as_array()
                .expect("fail-closed conditions")
                .iter()
                .any(|condition| condition == "missing or dirty reviewed-commit provenance")
        );

        let proof_blocker = value["blockers"]
            .as_array()
            .expect("blockers")
            .iter()
            .find(|blocker| {
                blocker["dimension_id"] == PROOF_FUNCTIONAL_DIMENSION_ID
                    && blocker["message"]
                        .as_str()
                        .is_some_and(|message| message.contains("program-index proof-design JSON"))
            })
            .expect("default report should include proof functional evidence blocker");
        assert!(
            proof_blocker["action"]
                .as_str()
                .is_some_and(|action| action.contains(PROOF_FUNCTIONAL_EVIDENCE_COMMAND)
                    && action.contains(PROOF_FUNCTIONAL_REPORT_FLAG))
        );
    }

    #[test]
    fn default_report_metadata_names_proof_concurrency_requirement() {
        let report = evaluate_suite(
            Some("default".to_string()),
            EffectivePolicy::from_input(&PolicyInput::default()),
            default_launch_dimensions(),
            None,
        );
        let value = serde_json::to_value(&report).expect("report should serialize");
        let requirement = &value["evidence_requirements"]["proof_concurrency"];

        assert_eq!(requirement["dimension_id"], PROOF_CONCURRENCY_DIMENSION_ID);
        assert_eq!(requirement["required_flag"], PROOF_CONCURRENCY_REPORT_FLAG);
        assert_eq!(requirement["required_command"], PROOF_CONCURRENCY_EVIDENCE_COMMAND);
        assert_eq!(requirement["expected_schema"], PROOF_CONCURRENCY_REPORT_SCHEMA);
        assert_eq!(requirement["current_json_required"], true);
        let required_kinds =
            requirement["required_obligation_kinds"].as_array().expect("required kinds");
        for required in PROOF_CONCURRENCY_REQUIRED_OBLIGATION_KINDS {
            assert!(
                required_kinds.iter().any(|kind| kind.as_str() == Some(required)),
                "missing required concurrency obligation kind {required}"
            );
        }
        let fail_closed_conditions =
            requirement["fail_closed_conditions"].as_array().expect("fail-closed conditions");
        for expected in [
            "manual or stale dimension without current proof-concurrency report JSON",
            "unknown JSON fields",
            "non-proved, skipped, unsupported, runtime_checked, timed_out, unknown, or failed obligation",
            "manual_pass obligation or summary counter",
            "summary counters not corroborated by obligation rows",
        ] {
            assert!(
                fail_closed_conditions.iter().any(|condition| condition.as_str() == Some(expected)),
                "missing proof-concurrency fail-closed condition {expected}"
            );
        }

        let proof_blocker = value["blockers"]
            .as_array()
            .expect("blockers")
            .iter()
            .find(|blocker| {
                blocker["dimension_id"] == PROOF_CONCURRENCY_DIMENSION_ID
                    && blocker["message"]
                        .as_str()
                        .is_some_and(|message| message.contains("proof-concurrency report JSON"))
            })
            .expect("default report should include proof-concurrency evidence blocker");
        assert!(
            proof_blocker["action"]
                .as_str()
                .is_some_and(|action| action.contains(PROOF_CONCURRENCY_EVIDENCE_COMMAND)
                    && action.contains(PROOF_CONCURRENCY_REPORT_FLAG))
        );
    }

    #[test]
    fn default_report_metadata_names_binary_source_roundtrip_requirement() {
        let report = evaluate_suite(
            Some("default".to_string()),
            EffectivePolicy::from_input(&PolicyInput::default()),
            default_launch_dimensions(),
            None,
        );
        let value = serde_json::to_value(&report).expect("report should serialize");
        let requirement = &value["evidence_requirements"]["proof_binary_source_roundtrip"];

        assert_eq!(requirement["dimension_id"], PRODUCT_PROOF_BINARY_ROUNDTRIP_DIMENSION_ID);
        assert_eq!(requirement["required_flag"], PRODUCT_PROOF_RELEASE_REPORT_FLAG);
        assert_eq!(
            requirement["required_command"],
            "targo trust release check --profile product-proof --visibility public --json"
        );
        assert_eq!(requirement["expected_schema"], RELEASE_REPORT_SCHEMA);
        assert_eq!(requirement["required_profile"], "product-proof");
        assert_eq!(requirement["required_gate"], "product-proof-coverage");
        assert_eq!(
            requirement["required_product_proof_component"],
            PRODUCT_PROOF_BINARY_DECOMP_COMPONENT
        );
        assert_eq!(requirement["required_product_proof_component_status"], "accepted");
        assert_eq!(requirement["required_compile_back_evidence_declaration"], true);
        assert_eq!(requirement["materialized_artifacts_required"], true);
        assert_eq!(
            requirement["materialized_artifact_reference_format"],
            "<compile-back-evidence-kind>:<relative-artifact-path>"
        );
        assert_eq!(requirement["current_json_required"], true);

        let required_kinds = requirement["required_compile_back_evidence_kinds"]
            .as_array()
            .expect("compile-back evidence kinds");
        assert_eq!(required_kinds.len(), COMPILE_BACK_REQUIRED_EVIDENCE.len());
        for required in COMPILE_BACK_REQUIRED_EVIDENCE {
            assert!(
                required_kinds.iter().any(|kind| kind.as_str() == Some(required)),
                "missing compile-back evidence kind {required}"
            );
        }

        let fail_closed_conditions =
            requirement["fail_closed_conditions"].as_array().expect("fail-closed conditions");
        for required in [
            "manual or stale dimension without current product-proof release report JSON",
            "missing product-proof component declaration",
            "missing compile-back evidence kind declaration",
            "missing materialized compile-back artifact reference",
        ] {
            assert!(
                fail_closed_conditions.iter().any(|condition| condition.as_str() == Some(required)),
                "missing fail-closed condition {required}"
            );
        }

        let product_proof_blocker = value["blockers"]
            .as_array()
            .expect("blockers")
            .iter()
            .find(|blocker| {
                blocker["dimension_id"] == PRODUCT_PROOF_BINARY_ROUNDTRIP_DIMENSION_ID
                    && blocker["message"].as_str().is_some_and(|message| {
                        message.contains("product-proof release report JSON")
                    })
            })
            .expect("default report should include product-proof release-report evidence blocker");
        assert!(
            product_proof_blocker["action"]
                .as_str()
                .is_some_and(|action| action.contains(
                    "targo trust release check --profile product-proof --visibility public --json"
                ) && action.contains(PRODUCT_PROOF_RELEASE_REPORT_FLAG))
        );
    }

    #[test]
    fn proof_functional_ingests_clean_program_index_proof_design_report() {
        let root = temp_repo_root("proof-functional-clean");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &proof_program_index_report(
                vec![
                    proof_row("proof_div_zero.good", "good", "verify_pass", 1, 1, 0, 0, 0),
                    proof_row("proof_div_zero.flawed", "flawed", "verify_fail", 1, 0, 1, 0, 0),
                ],
                2,
            ),
        );

        let dimension =
            read_proof_functional_program_index_report(&path).expect("clean report should ingest");
        assert_eq!(dimension.id, PROOF_FUNCTIONAL_DIMENSION_ID);
        assert_eq!(dimension.status, Some(DeclaredStatus::Pass));
        assert_eq!(dimension.rust_value, Some(0.0));
        assert_eq!(dimension.trust_value, Some(2.0));
        assert!(dimension.evidence.iter().any(|item| {
            item.contains(PROGRAM_INDEX_REPORT_SCHEMA)
                && item.contains("proof_design_rows=2")
                && item.contains("obligations=2")
        }));

        let report = suite_with(vec![dimension]);
        assert_eq!(report.dimensions[0].status, DimensionStatus::Pass);
        assert!(report.dimensions[0].trust_is_better);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_functional_requires_bound_frontend_native_evidence() {
        let root = temp_repo_root("proof-functional-frontend-native-evidence");
        let path = root.join("program-index-report.json");
        let mut report = proof_program_index_report(
            vec![
                proof_row("proof_div_zero.good", "good", "verify_pass", 1, 1, 0, 0, 0),
                proof_row("proof_div_zero.flawed", "flawed", "verify_fail", 1, 0, 1, 0, 0),
            ],
            2,
        );
        report["results"][0]["transport"]["native_trust_ir_results"] = serde_json::json!(0);
        write_json(&path, &report);

        let dimension =
            read_proof_functional_program_index_report(&path).expect("report should parse");
        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("typed TrustIr verifier-ingress evidence must cover every obligation")
                && hint.contains("must match proof-design rows")
        }));

        report["summary"]
            .as_object_mut()
            .expect("summary object")
            .remove("unsupported_frontend_lowering_gate");
        write_json(&path, &report);
        let missing =
            read_proof_functional_program_index_report(&path).expect("report should parse");
        assert_eq!(missing.status, Some(DeclaredStatus::Fail));
        assert!(missing.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("unsupported_frontend_lowering_gate.schema must be")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_functional_rejects_candidate_program_index_evidence_metadata() {
        let root = temp_repo_root("proof-functional-candidate-evidence");
        let path = root.join("program-index-report.json");
        let mut report = proof_program_index_report(
            vec![
                proof_row("proof_div_zero.good", "good", "verify_pass", 1, 1, 0, 0, 0),
                proof_row("proof_div_zero.flawed", "flawed", "verify_fail", 1, 0, 1, 0, 0),
            ],
            2,
        );
        report["program_index_evidence"]["status"] = serde_json::json!("candidate_non_gating");
        report["program_index_evidence"]["admissible_for_domination"] = serde_json::json!(false);
        report["program_index_evidence"]["selected_candidate_rows"] = serde_json::json!(2);
        report["program_index_evidence"]["selected_gating_rows"] = serde_json::json!(0);
        report["program_index_evidence"]["selected_admissible_gating_rows"] = serde_json::json!(0);
        report["program_index_evidence"]["selected_suites"]["proof-design"]["candidate_rows"] =
            serde_json::json!(2);
        report["program_index_evidence"]["selected_suites"]["proof-design"]["candidate_evidence"] =
            serde_json::json!(true);
        write_json(&path, &report);

        let dimension =
            read_proof_functional_program_index_report(&path).expect("report should parse");
        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("program_index_evidence.admissible_for_domination must be true")
                && hint.contains("selected_candidate_rows must be 0")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_functional_requires_program_index_evidence_metadata() {
        let root = temp_repo_root("proof-functional-missing-evidence-metadata");
        let path = root.join("program-index-report.json");
        let mut report = proof_program_index_report(
            vec![
                proof_row("proof_div_zero.good", "good", "verify_pass", 1, 1, 0, 0, 0),
                proof_row("proof_div_zero.flawed", "flawed", "verify_fail", 1, 0, 1, 0, 0),
            ],
            2,
        );
        report.as_object_mut().expect("report object").remove("program_index_evidence");
        write_json(&path, &report);

        let dimension =
            read_proof_functional_program_index_report(&path).expect("report should parse");
        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(
            dimension
                .ai_hint
                .as_deref()
                .is_some_and(|hint| { hint.contains("program_index_evidence must be present") })
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_functional_zero_obligation_program_index_report_fails_closed() {
        let root = temp_repo_root("proof-functional-zero-obligation");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &proof_program_index_report(
                vec![
                    proof_row("proof_div_zero.good", "good", "verify_pass", 0, 0, 0, 0, 0),
                    proof_row("proof_div_zero.flawed", "flawed", "verify_fail", 1, 0, 1, 0, 0),
                ],
                2,
            ),
        );

        let dimension =
            read_proof_functional_program_index_report(&path).expect("report should parse");
        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains(PROOF_FUNCTIONAL_EVIDENCE_COMMAND)
                && hint.contains("transport must report at least one obligation")
        }));

        let report = suite_with(vec![dimension]);
        assert_eq!(report.dimensions[0].status, DimensionStatus::Fail);
        assert!(report.blockers.iter().any(|blocker| {
            blocker.dimension_id.as_deref() == Some(PROOF_FUNCTIONAL_DIMENSION_ID)
                && blocker.kind == BlockerKind::DeclaredFailure
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_functional_partial_good_row_fails_closed() {
        let root = temp_repo_root("proof-functional-partial-good");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &proof_program_index_report(
                vec![
                    proof_row("proof_div_zero.good", "good", "verify_pass", 2, 1, 0, 0, 0),
                    proof_row("proof_div_zero.flawed", "flawed", "verify_fail", 1, 0, 1, 0, 0),
                ],
                2,
            ),
        );

        let dimension =
            read_proof_functional_program_index_report(&path).expect("report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("good proof row must prove all obligations")
                && hint.contains(PROOF_FUNCTIONAL_EVIDENCE_COMMAND)
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_functional_mismatched_transport_counters_fail_closed() {
        let root = temp_repo_root("proof-functional-mismatched-transport");
        let path = root.join("program-index-report.json");
        let mut report = proof_program_index_report(
            vec![
                proof_row("proof_div_zero.good", "good", "verify_pass", 1, 1, 0, 0, 0),
                proof_row("proof_div_zero.flawed", "flawed", "verify_fail", 1, 0, 1, 0, 0),
            ],
            2,
        );
        report["results"][0]["transport"]["proved_results"] = serde_json::json!(0);
        write_json(&path, &report);

        let dimension =
            read_proof_functional_program_index_report(&path).expect("report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert_eq!(dimension.rust_value, None);
        assert_eq!(dimension.trust_value, None);
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("transport.proved=1 must match transport.proved_results=0")
                && hint.contains(PROOF_FUNCTIONAL_EVIDENCE_COMMAND)
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_functional_summary_failures_block_clean_rows() {
        let root = temp_repo_root("proof-functional-summary-failed");
        let path = root.join("program-index-report.json");
        let mut report = proof_program_index_report(
            vec![
                proof_row("proof_div_zero.good", "good", "verify_pass", 1, 1, 0, 0, 0),
                proof_row("proof_div_zero.flawed", "flawed", "verify_fail", 1, 0, 1, 0, 0),
            ],
            2,
        );
        report["summary"]["failed"] = serde_json::json!(1);
        write_json(&path, &report);

        let dimension =
            read_proof_functional_program_index_report(&path).expect("report should parse");
        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(
            dimension
                .ai_hint
                .as_deref()
                .is_some_and(|hint| hint.contains("summary.failed must be 0"))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_functional_report_requires_clean_reviewed_commit_provenance() {
        let root = temp_repo_root("proof-functional-dirty-provenance");
        let path = root.join("program-index-report.json");
        let mut report = proof_program_index_report(
            vec![
                proof_row("proof_div_zero.good", "good", "verify_pass", 1, 1, 0, 0, 0),
                proof_row("proof_div_zero.flawed", "flawed", "verify_fail", 1, 0, 1, 0, 0),
            ],
            2,
        );
        report["repo_dirty"] = serde_json::json!(true);
        write_json(&path, &report);

        let dimension =
            read_proof_functional_program_index_report(&path).expect("report should parse");
        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert_eq!(dimension.rust_value, None);
        assert_eq!(dimension.trust_value, None);
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("repo_dirty must be false")
                && hint.contains(PROOF_FUNCTIONAL_EVIDENCE_COMMAND)
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn proof_functional_missing_proof_design_rows_is_actionable_unknown() {
        let root = temp_repo_root("proof-functional-missing-rows");
        let path = root.join("program-index-report.json");
        write_json(&path, &proof_program_index_report(Vec::new(), 0));

        let dimension =
            read_proof_functional_program_index_report(&path).expect("report should parse");
        assert_eq!(dimension.status, Some(DeclaredStatus::Unknown));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("no proof-design trust-verify rows")
                && hint.contains(PROOF_FUNCTIONAL_EVIDENCE_COMMAND)
        }));

        let report = suite_with(vec![dimension]);
        assert_eq!(report.dimensions[0].status, DimensionStatus::Unknown);
        assert!(report.blockers.iter().any(|blocker| {
            blocker.dimension_id.as_deref() == Some(PROOF_FUNCTIONAL_DIMENSION_ID)
                && blocker.kind == BlockerKind::UnknownResult
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_classifies_target_arch_dimensions() {
        let root = temp_repo_root("program-index-runtime-binary");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &runtime_program_index_report(
                vec![
                    runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                    runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
                ],
                Some("x86_64-unknown-linux-gnu"),
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        let binary = dimensions
            .iter()
            .find(|dimension| dimension.id == "efficiency.x86_64.binary-size")
            .expect("x86 binary-size dimension");
        assert_eq!(runtime.status, None);
        assert_eq!(runtime.rust_value, Some(1.0));
        assert!(runtime.trust_value.is_some_and(|value| value > 1.9));
        assert_eq!(binary.status, None);
        assert!(binary.rust_value.is_some_and(|value| (value - 100.0).abs() < 0.000001));
        assert!(binary.trust_value.is_some_and(|value| (value - 80.0).abs() < 0.000001));

        let report = suite_with(dimensions);
        assert!(
            report
                .dimensions
                .iter()
                .filter(|dimension| matches!(
                    dimension.id.as_str(),
                    "runtime.x86_64.geomean" | "efficiency.x86_64.binary-size"
                ))
                .all(|dimension| dimension.status == DimensionStatus::Pass
                    && dimension.trust_is_better)
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_blocked_upstream_baseline() {
        let root = temp_repo_root("program-index-runtime-blocked-baseline");
        let path = root.join("program-index-report.json");
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some("x86_64-unknown-linux-gnu"),
        );
        report["upstream_baseline"]["status"] = serde_json::json!("blocked");
        report["upstream_baseline"]["entries"][0]["status"] = serde_json::json!("blocked");
        report["upstream_baseline"]["entries"][0]["blockers"] =
            serde_json::json!(["upstream-rustc baseline binary is inside this Trust checkout"]);
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");

        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert!(runtime.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("upstream_baseline.status must be passed")
                && hint.contains("upstream-rustc baseline entry status must be passed")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_non_ready_trust_unlock_path() {
        let root = temp_repo_root("program-index-runtime-blocked-unlock-path");
        let path = root.join("program-index-report.json");
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some("x86_64-unknown-linux-gnu"),
        );
        report["trust_unlock_path"]["status"] =
            serde_json::json!("blocked_noncanonical_entrypoints");
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");

        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert!(runtime.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("trust_unlock_path.status must be ready_for_trust_compile_evidence")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_stale_runtime_summary_counts() {
        let root = temp_repo_root("program-index-runtime-stale-summary");
        let path = root.join("program-index-report.json");
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some("x86_64-unknown-linux-gnu"),
        );
        report["runtime_parity"]["summary"]["comparison_passed"] = serde_json::json!(99);
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");

        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert!(runtime.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("runtime_parity.summary.comparison_passed declares 99")
                && hint.contains("rows imply 1")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_non_canonical_executable_hash() {
        let root = temp_repo_root("program-index-runtime-bad-executable-hash");
        let path = root.join("program-index-report.json");
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some("x86_64-unknown-linux-gnu"),
        );
        report["runtime_parity"]["rows"][1]["executable_sha256"] =
            serde_json::json!("trust-slot-sha256");
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let binary = dimensions
            .iter()
            .find(|dimension| dimension.id == "efficiency.x86_64.binary-size")
            .expect("x86 binary-size dimension");

        assert_eq!(binary.status, Some(DeclaredStatus::Fail));
        assert!(binary.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("Trust executable_sha256 must be a canonical SHA-256 hash")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_classifies_clean_compile_dimension() {
        let root = temp_repo_root("program-index-clean-compile-pass");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &compile_program_index_report(
                vec![
                    compile_row(
                        PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                        CompileEvidenceMode::CleanRelease,
                        2.0,
                        1.2,
                        0.3,
                        2_000_000,
                    ),
                    compile_row(
                        PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
                        CompileEvidenceMode::CleanRelease,
                        1.0,
                        0.7,
                        0.2,
                        1_000_000,
                    ),
                ],
                "x86_64-unknown-linux-gnu",
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("compile report should parse");
        let clean = dimensions
            .iter()
            .find(|dimension| dimension.id == "compile.x86_64.clean-release")
            .expect("x86 clean compile dimension");
        assert_eq!(clean.status, None);
        assert!(clean.rust_value.is_some_and(|value| (value - 2000.0).abs() < 0.000001));
        assert!(clean.trust_value.is_some_and(|value| (value - 1000.0).abs() < 0.000001));
        assert!(clean.evidence.iter().any(|item| {
            item.contains("rust_cpu_seconds_geomean=1.500000")
                && item.contains("trust_peak_rss_geomean=1000000")
        }));

        let report = suite_with(dimensions);
        let clean = report
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "compile.x86_64.clean-release")
            .expect("x86 clean compile report row");
        assert_eq!(clean.status, DimensionStatus::Pass);
        assert!(clean.trust_is_better);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_requires_strict_performance_evidence_lane() {
        let mut report = clean_compile_program_index_report();
        report
            .as_object_mut()
            .expect("report object")
            .remove("strict_superiority_performance_evidence");
        report["summary"]
            .as_object_mut()
            .expect("summary object")
            .remove("strict_superiority_performance_evidence");

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-missing-strict-lane", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &["strict_superiority_performance_evidence must be present"],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_non_strict_performance_lane_comparison() {
        let mut report = clean_compile_program_index_report();
        report["strict_superiority_performance_evidence"]["lanes"]["clean_release_compile"]["comparisons"]
            [0]["trust_strictly_better"] = serde_json::json!(false);

        let (root, clean) = read_x86_clean_compile_dimension(
            "program-index-compile-nonstrict-strict-lane",
            &report,
        );

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "strict_superiority_performance_evidence.lanes.clean_release_compile.comparisons[trust-noverify].trust_strictly_better must be true",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_classifies_incremental_compile_dimension() {
        let root = temp_repo_root("program-index-incremental-compile-pass");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &compile_program_index_report(
                vec![
                    compile_row(
                        PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                        CompileEvidenceMode::IncrementalDebug,
                        1.5,
                        0.8,
                        0.2,
                        1_500_000,
                    ),
                    compile_row(
                        PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
                        CompileEvidenceMode::IncrementalDebug,
                        0.75,
                        0.5,
                        0.1,
                        900_000,
                    ),
                ],
                "aarch64-apple-darwin",
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("compile report should parse");
        let incremental = dimensions
            .iter()
            .find(|dimension| dimension.id == "compile.aarch64.incremental-debug")
            .expect("aarch64 incremental compile dimension");
        assert_eq!(incremental.status, None);
        assert!(incremental.evidence.iter().any(|item| item.contains("mode=warm-incremental")));

        let report = suite_with(dimensions);
        let incremental = report
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "compile.aarch64.incremental-debug")
            .expect("aarch64 incremental compile report row");
        assert_eq!(incremental.status, DimensionStatus::Pass);
        assert!(incremental.trust_is_better);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn domination_ingests_strict_runtime_binary_reports_for_both_launch_arches() {
        let root = temp_repo_root("domination-strict-runtime-binary-arches");
        let x86_path = root.join("program-index-runtime-x86.json");
        let aarch64_path = root.join("program-index-runtime-aarch64.json");
        write_json(
            &x86_path,
            &runtime_program_index_report(
                vec![
                    runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                    runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
                ],
                Some("x86_64-unknown-linux-gnu"),
            ),
        );
        write_json(
            &aarch64_path,
            &runtime_program_index_report(
                vec![
                    runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 4.0, 200),
                    runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 2.0, 120),
                ],
                Some("aarch64-apple-darwin"),
            ),
        );

        let report = build_report(&RustVsTrustArgs {
            format: OutputFormat::Json,
            suite: None,
            compat_summary: Vec::new(),
            proof_program_index_report: None,
            proof_unsafe_memory_report: None,
            proof_concurrency_report: None,
            program_index_benchmark_report: vec![x86_path, aarch64_path],
            product_proof_release_report: None,
            out: None,
            write_template: None,
            allow_missing_evidence: false,
            allow_exceptions: false,
            min_performance_advantage_pct: None,
        })
        .expect("strict runtime/binary reports should ingest");

        for id in [
            "runtime.x86_64.geomean",
            "efficiency.x86_64.binary-size",
            "runtime.aarch64.geomean",
            "efficiency.aarch64.binary-size",
        ] {
            assert!(
                report.dimensions.iter().any(
                    |dimension| dimension.id == id && dimension.status == DimensionStatus::Pass
                ),
                "{id} should pass with strict performance evidence"
            );
        }

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn domination_combines_cold_and_warm_program_index_reports() {
        let root = temp_repo_root("domination-program-index-cold-warm");
        let cold_path = root.join("program-index-cold.json");
        let warm_path = root.join("program-index-warm.json");
        write_json(&cold_path, &clean_compile_program_index_report());
        write_json(
            &warm_path,
            &compile_program_index_report(
                vec![
                    compile_row(
                        PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                        CompileEvidenceMode::IncrementalDebug,
                        1.5,
                        0.8,
                        0.2,
                        1_500_000,
                    ),
                    compile_row(
                        PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
                        CompileEvidenceMode::IncrementalDebug,
                        0.75,
                        0.5,
                        0.1,
                        900_000,
                    ),
                ],
                "x86_64-unknown-linux-gnu",
            ),
        );

        let report = build_report(&RustVsTrustArgs {
            format: OutputFormat::Json,
            suite: None,
            compat_summary: Vec::new(),
            proof_program_index_report: None,
            proof_unsafe_memory_report: None,
            proof_concurrency_report: None,
            program_index_benchmark_report: vec![cold_path, warm_path],
            product_proof_release_report: None,
            out: None,
            write_template: None,
            allow_missing_evidence: false,
            allow_exceptions: false,
            min_performance_advantage_pct: None,
        })
        .expect("multiple program-index benchmark reports should ingest");

        assert!(report.dimensions.iter().any(|dimension| {
            dimension.id == "compile.x86_64.clean-release"
                && dimension.status == DimensionStatus::Pass
        }));
        assert!(report.dimensions.iter().any(|dimension| {
            dimension.id == "compile.x86_64.incremental-debug"
                && dimension.status == DimensionStatus::Pass
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_mismatched_source_identity() {
        let mut report = clean_compile_program_index_report();
        report["results"][1]["source_sha256"] =
            serde_json::json!("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-source-mismatch", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: compile source identity field source_sha256 must be present and equal",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_stale_compile_profile_summary() {
        let root = temp_repo_root("program-index-compile-stale-summary");
        let path = root.join("program-index-report.json");
        let mut report = clean_compile_program_index_report();
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["measured_non_incremental_rows"] =
            serde_json::json!(0);
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("compile report should parse");
        let clean = dimensions
            .iter()
            .find(|dimension| dimension.id == "compile.x86_64.clean-release")
            .expect("x86 clean compile dimension");

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert!(clean.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("measurement_profiles.measured_non_incremental_rows declares 0")
                && hint.contains("rows imply 2")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_stale_compile_profile_schema() {
        let mut report = clean_compile_program_index_report();
        report["summary"]["compile_resource_usage"]["measurement_profiles"]["schema"] =
            serde_json::json!("trust.program-index.compile-measurement-profile.v0");

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-stale-profile-schema", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert!(clean.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains(
                "summary.compile_resource_usage.measurement_profiles.schema must be trust.program-index.compile-measurement-profile.v1",
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_missing_compile_cpu_usage() {
        let mut report = clean_compile_program_index_report();
        report["results"][1]["resource_usage"]["user_cpu_seconds"] = Value::Null;

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-missing-cpu", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: Trust resource_usage user_cpu_seconds/system_cpu_seconds must be present",
                "(slot=trust-noverify measurement_profile.mode=cold-artifact)",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_missing_compile_elapsed_seconds() {
        let mut report = clean_compile_program_index_report();
        report["results"][0]["resource_usage"]["elapsed_seconds"] = Value::Null;

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-missing-elapsed", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: baseline resource_usage.elapsed_seconds must be positive",
                "(slot=upstream-rustc measurement_profile.mode=cold-artifact)",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_missing_compile_peak_rss() {
        let mut report = clean_compile_program_index_report();
        report["results"][1]["peak_rss_bytes"] = Value::Null;
        report["results"][1]["resource_usage"]["peak_rss_bytes"] = Value::Null;
        let rows = report["results"].as_array().expect("compile rows").clone();
        report["summary"]["compile_resource_usage"] =
            serde_json::json!(compile_resource_summary_fixture(&rows));

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-missing-peak-rss", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: Trust resource_usage.peak_rss_bytes must be positive",
                "compile-perf:good:compile_hello.good: Trust peak_rss_bytes must be positive",
                "(slot=trust-noverify measurement_profile.mode=cold-artifact)",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_self_reported_resource_usage_source() {
        let mut report = clean_compile_program_index_report();
        report["results"][1]["resource_usage"]["source"] = serde_json::json!("self-reported");

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-self-reported-source", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: Trust resource_usage.source must be os.wait4 for compile resource evidence",
                "(slot=trust-noverify measurement_profile.mode=cold-artifact)",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_missing_compile_peak_rss_raw() {
        let mut report = clean_compile_program_index_report();
        report["results"][0]["resource_usage"]["peak_rss_raw"] = Value::Null;

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-missing-peak-rss-raw", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: baseline resource_usage.peak_rss_raw must be positive",
                "(slot=upstream-rustc measurement_profile.mode=cold-artifact)",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_invalid_compile_peak_rss_raw_unit() {
        let mut report = clean_compile_program_index_report();
        report["results"][1]["resource_usage"]["peak_rss_raw_unit"] = serde_json::json!("pages");

        let (root, clean) = read_x86_clean_compile_dimension(
            "program-index-compile-invalid-peak-rss-raw-unit",
            &report,
        );

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: Trust resource_usage.peak_rss_raw_unit must be bytes or kilobytes, got `pages`",
                "(slot=trust-noverify measurement_profile.mode=cold-artifact)",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_stale_peak_rss_raw_binding() {
        let mut report = clean_compile_program_index_report();
        report["results"][1]["resource_usage"]["peak_rss_raw"] = serde_json::json!(1);
        report["results"][1]["resource_usage"]["peak_rss_raw_unit"] =
            serde_json::json!("kilobytes");

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-stale-peak-rss-raw", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: Trust resource_usage.peak_rss_bytes 1000000 must match peak_rss_raw 1 kilobytes normalized to 1024",
                "(slot=trust-noverify measurement_profile.mode=cold-artifact)",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_trust_compile_cpu_regression() {
        let mut report = clean_compile_program_index_report();
        report["results"][1]["resource_usage"]["user_cpu_seconds"] = serde_json::json!(1.3);
        report["results"][1]["resource_usage"]["system_cpu_seconds"] = serde_json::json!(0.3);

        let (root, clean) =
            read_x86_clean_compile_dimension("program-index-compile-cpu-regression", &report);

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert!(clean.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains(
                "compile-perf:good:compile_hello.good: Trust compile CPU time 1.600000s must beat rustc 1.500000s",
            )
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_stale_elapsed_resource_usage_binding() {
        let mut report = clean_compile_program_index_report();
        report["results"][1]["resource_usage"]["elapsed_seconds"] = serde_json::json!(1.5);

        let (root, clean) = read_x86_clean_compile_dimension(
            "program-index-compile-stale-elapsed-resource-binding",
            &report,
        );

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: Trust duration_seconds 1.000000s must match resource_usage.elapsed_seconds 1.500000s",
                "(slot=trust-noverify measurement_profile.mode=cold-artifact)",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_compile_report_rejects_stale_resource_usage_binding() {
        let mut report = clean_compile_program_index_report();
        report["results"][1]["resource_usage"]["peak_rss_bytes"] = serde_json::json!(3_000_000);

        let (root, clean) = read_x86_clean_compile_dimension(
            "program-index-compile-stale-resource-binding",
            &report,
        );

        assert_eq!(clean.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            &clean,
            &[
                "compile-perf:good:compile_hello.good: Trust peak_rss_bytes 1000000 must match resource_usage.peak_rss_bytes 3000000",
                "(slot=trust-noverify measurement_profile.mode=cold-artifact)",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_requires_target_arch_metadata() {
        let root = temp_repo_root("program-index-runtime-missing-target");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &runtime_program_index_report(
                vec![
                    runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                    runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
                ],
                None,
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        assert!(dimensions.iter().any(|dimension| {
            dimension.id == "runtime.x86_64.geomean"
                && dimension.status == Some(DeclaredStatus::Fail)
                && dimension.ai_hint.as_deref().is_some_and(|hint| hint.contains("target_arch"))
        }));
        assert!(dimensions.iter().any(|dimension| {
            dimension.id == "runtime.aarch64.geomean"
                && dimension.status == Some(DeclaredStatus::Fail)
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_dirty_repo_provenance() {
        let root = temp_repo_root("program-index-runtime-dirty-repo");
        let path = root.join("program-index-report.json");
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some("x86_64-unknown-linux-gnu"),
        );
        report["repo_dirty"] = serde_json::json!(true);
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        let binary = dimensions
            .iter()
            .find(|dimension| dimension.id == "efficiency.x86_64.binary-size")
            .expect("x86 binary-size dimension");
        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert_eq!(binary.status, Some(DeclaredStatus::Fail));
        assert!(
            runtime
                .ai_hint
                .as_deref()
                .is_some_and(|hint| hint.contains("repo_dirty must be false"))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_requires_proof_grade_dirty_metadata() {
        let root = temp_repo_root("program-index-runtime-weak-dirty-metadata");
        let path = root.join("program-index-report.json");
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some("x86_64-unknown-linux-gnu"),
        );
        report["repo_dirty_metadata"]["untracked_files"] = serde_json::json!("included");
        report["repo_dirty_metadata"]
            .as_object_mut()
            .expect("metadata object")
            .remove("ignore_submodules");
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            runtime,
            &["untracked_files must be all", "ignore_submodules=none"],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_mismatched_runtime_summary_counts() {
        let root = temp_repo_root("program-index-runtime-summary-counts");
        let path = root.join("program-index-report.json");
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some("x86_64-unknown-linux-gnu"),
        );
        report["runtime_parity"]["summary"]["comparison_passed"] = serde_json::json!(0);
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        let binary = dimensions
            .iter()
            .find(|dimension| dimension.id == "efficiency.x86_64.binary-size")
            .expect("x86 binary-size dimension");
        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert_eq!(binary.status, Some(DeclaredStatus::Fail));
        assert!(
            runtime
                .ai_hint
                .as_deref()
                .is_some_and(|hint| { hint.contains("runtime_parity.summary.comparison_passed") })
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_any_slow_trust_runtime_pair() {
        let root = temp_repo_root("program-index-runtime-pair-regression");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &runtime_program_index_report(
                vec![
                    runtime_row_for(
                        "runtime_fast.good",
                        PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                        10.0,
                        100,
                    ),
                    runtime_row_for("runtime_fast.good", PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
                    runtime_row_for(
                        "runtime_slow.good",
                        PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                        1.0,
                        100,
                    ),
                    runtime_row_for("runtime_slow.good", PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 2.0, 80),
                ],
                Some("x86_64-unknown-linux-gnu"),
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            runtime,
            &[
                "runtime:good:runtime_slow.good: Trust run_duration_seconds 2.000000s must be strictly less than baseline 1.000000s",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_any_larger_trust_binary_pair() {
        let root = temp_repo_root("program-index-binary-pair-regression");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &runtime_program_index_report(
                vec![
                    runtime_row_for(
                        "runtime_small.good",
                        PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                        10.0,
                        1000,
                    ),
                    runtime_row_for("runtime_small.good", PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 1),
                    runtime_row_for(
                        "runtime_large.good",
                        PROGRAM_INDEX_RUNTIME_BASELINE_SLOT,
                        2.0,
                        100,
                    ),
                    runtime_row_for(
                        "runtime_large.good",
                        PROGRAM_INDEX_RUNTIME_TRUST_SLOT,
                        1.0,
                        200,
                    ),
                ],
                Some("x86_64-unknown-linux-gnu"),
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        let binary = dimensions
            .iter()
            .find(|dimension| dimension.id == "efficiency.x86_64.binary-size")
            .expect("x86 binary-size dimension");
        assert_eq!(runtime.status, None);
        assert_eq!(binary.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            binary,
            &[
                "runtime:good:runtime_large.good: Trust executable_size_bytes 200 must be strictly smaller than baseline 100",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_mismatched_source_identity() {
        let root = temp_repo_root("program-index-runtime-source-mismatch");
        let path = root.join("program-index-report.json");
        let mut trust_row = runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80);
        trust_row["source_sha256"] =
            serde_json::json!("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        write_json(
            &path,
            &runtime_program_index_report(
                vec![runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100), trust_row],
                Some("x86_64-unknown-linux-gnu"),
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        let binary = dimensions
            .iter()
            .find(|dimension| dimension.id == "efficiency.x86_64.binary-size")
            .expect("x86 binary-size dimension");
        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert_eq!(binary.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            runtime,
            &[
                "runtime:good:runtime_hello.good: runtime source identity field source_sha256 must be present and equal",
            ],
        );
        assert_dimension_hint_contains(
            binary,
            &["no comparable executable size pairs were present"],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_noncanonical_runtime_hashes() {
        let root = temp_repo_root("program-index-runtime-bad-runtime-hash");
        let path = root.join("program-index-report.json");
        let mut trust_row = runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80);
        trust_row["run_stdout_sha256"] = serde_json::json!("not-a-sha256");
        write_json(
            &path,
            &runtime_program_index_report(
                vec![runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100), trust_row],
                Some("x86_64-unknown-linux-gnu"),
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert!(runtime.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("canonical runtime stdout/stderr SHA-256 hashes")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_rejects_noncanonical_executable_hashes() {
        let root = temp_repo_root("program-index-runtime-bad-executable-hash");
        let path = root.join("program-index-report.json");
        let mut trust_row = runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80);
        trust_row["executable_sha256"] = serde_json::json!("not-a-sha256");
        write_json(
            &path,
            &runtime_program_index_report(
                vec![runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100), trust_row],
                Some("x86_64-unknown-linux-gnu"),
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        let binary = dimensions
            .iter()
            .find(|dimension| dimension.id == "efficiency.x86_64.binary-size")
            .expect("x86 binary-size dimension");
        assert_eq!(runtime.status, None);
        assert_eq!(binary.status, Some(DeclaredStatus::Fail));
        assert!(binary.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("executable_sha256 must be a canonical SHA-256 hash")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_requires_reviewed_commit_sha() {
        let root = temp_repo_root("program-index-runtime-missing-head");
        let path = root.join("program-index-report.json");
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some("x86_64-unknown-linux-gnu"),
        );
        report["repo_head"] = serde_json::json!("short-sha");
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");
        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert!(
            runtime
                .ai_hint
                .as_deref()
                .is_some_and(|hint| hint.contains("repo_head must be a full git SHA"))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_report_rejects_strict_performance_arch_mismatch() {
        let root = temp_repo_root("program-index-runtime-strict-arch-mismatch");
        let path = root.join("program-index-report.json");
        let mut report = runtime_program_index_report(
            vec![
                runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100),
                runtime_row(PROGRAM_INDEX_RUNTIME_TRUST_SLOT, 1.0, 80),
            ],
            Some("x86_64-unknown-linux-gnu"),
        );
        report["strict_superiority_performance_evidence"]["target_arch"] =
            serde_json::json!("aarch64");
        report["strict_superiority_performance_evidence"]["lanes"]["runtime_geomean"]["target_arch"] =
            serde_json::json!("aarch64");
        write_json(&path, &report);

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.x86_64.geomean")
            .expect("x86 runtime dimension");

        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert_dimension_hint_contains(
            runtime,
            &[
                "strict_superiority_performance_evidence.target_arch must match report architecture x86_64",
                "strict_superiority_performance_evidence.lanes.runtime_geomean.target_arch must match report architecture x86_64",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn program_index_runtime_binary_report_requires_trust_runtime_slot() {
        let root = temp_repo_root("program-index-runtime-missing-trust-slot");
        let path = root.join("program-index-report.json");
        write_json(
            &path,
            &runtime_program_index_report(
                vec![runtime_row(PROGRAM_INDEX_RUNTIME_BASELINE_SLOT, 2.0, 100)],
                Some("aarch64-apple-darwin"),
            ),
        );

        let dimensions =
            read_program_index_runtime_binary_report(&path).expect("runtime report should parse");
        let runtime = dimensions
            .iter()
            .find(|dimension| dimension.id == "runtime.aarch64.geomean")
            .expect("aarch64 runtime dimension");
        assert_eq!(runtime.status, Some(DeclaredStatus::Fail));
        assert!(
            runtime
                .ai_hint
                .as_deref()
                .is_some_and(|hint| hint.contains(PROGRAM_INDEX_RUNTIME_TRUST_SLOT))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn missing_required_evidence_is_unproven() {
        let mut dimension =
            numeric_dimension("proof.overflow", DimensionCategory::Verification, 0.0, 1.0);
        dimension.evidence.clear();
        let report = suite_with(vec![dimension]);

        assert_eq!(report.verdict, Verdict::Unproven);
        assert!(report.blockers.iter().any(|blocker| blocker.kind == BlockerKind::MissingEvidence));
    }

    #[test]
    fn performance_regression_is_not_superior() {
        let mut dimension =
            numeric_dimension("perf.clean-build", DimensionCategory::Performance, 100.0, 105.0);
        dimension.metric = Some(MetricKind::LatencyMs);
        dimension.higher_is_better = Some(false);
        let report = suite_with(vec![dimension]);

        assert_eq!(report.verdict, Verdict::NotSuperior);
        assert!(report.blockers.iter().any(|blocker| blocker.kind == BlockerKind::Regression));
    }

    #[test]
    fn compatibility_exception_from_summary_is_rejected_by_default() {
        let row = CompatibilityResultInput {
            baseline_entry_id: "toolchain.rustc".to_string(),
            outcome: CompatibilityOutcomeInput::Excepted,
            observed: None,
            exception_id: Some("ex1".to_string()),
            upstream_fix_id: None,
        };
        let mut compatible = 0;
        let mut non_compatible = 0;
        let mut unknown = 0;
        let (status, _, _) = match row.outcome {
            CompatibilityOutcomeInput::Compatible => {
                compatible += 1;
                (DeclaredStatus::Pass, String::new(), String::new())
            }
            CompatibilityOutcomeInput::Unknown => {
                unknown += 1;
                (DeclaredStatus::Unknown, String::new(), String::new())
            }
            CompatibilityOutcomeInput::Excepted
            | CompatibilityOutcomeInput::FixedUpstream
            | CompatibilityOutcomeInput::Divergent => {
                non_compatible += 1;
                (DeclaredStatus::Fail, String::new(), String::new())
            }
        };

        let report = suite_with(vec![DimensionInput {
            id: format!("compat.{}", row.baseline_entry_id),
            title: "compat exception".to_string(),
            category: DimensionCategory::Compatibility,
            metric: Some(MetricKind::PassRate),
            comparison_baseline: Some("fixture baseline".to_string()),
            required: true,
            rust_value: None,
            trust_value: None,
            higher_is_better: Some(true),
            min_trust_delta_pct: None,
            max_trust_regression_pct: None,
            status: Some(status),
            unit: None,
            weight: 1.0,
            evidence: vec!["fixture summary".to_string()],
            ai_hint: None,
            owner: None,
            evidence_source: DimensionEvidenceSource::Manual,
        }]);

        assert_eq!((compatible, non_compatible, unknown), (0, 1, 0));
        assert_eq!(report.verdict, Verdict::NotSuperior);
        assert!(
            report
                .blockers
                .iter()
                .any(|blocker| blocker.kind == BlockerKind::CompatibilityNotProven)
        );
    }

    #[test]
    fn compat_summary_ingestion_accepts_canonical_summary_and_preserves_observed_detail() {
        let root = temp_repo_root("compat-summary-canonical");
        let path = root.join("summary.json");
        fs::write(
            &path,
            r#"{
  "schema_version": "0.1.0",
  "baseline_id": "baseline.cli",
  "generated_on": "2026-04-26",
  "run_id": "ci-42",
  "repo_head": "0123456789abcdef0123456789abcdef01234567",
  "repo_dirty": false,
  "upstream_revision": "rust-lang/rust:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "runner": {
    "implementation": "rust",
    "entrypoint": "targo trust domination upstream-tests",
    "argv": ["targo", "trust", "domination", "upstream-tests", "--release", "--proof-mode", "full", "--execute", "--summary-out", "reports/upstream-rust/summary.json"],
    "release_evidence_contract": {
      "entrypoint": "targo trust domination upstream-tests",
      "release": true,
      "execute": true,
      "proof_mode": "full",
      "summary_out": "reports/upstream-rust/summary.json",
      "requires_release": true,
      "requires_execute": true,
      "requires_proof_mode": "full",
      "requires_summary_out": true,
      "satisfied": true
    },
    "python_used": false,
    "tool": "trust-upstream-compat"
  },
  "totals": {
    "total": 3,
    "compatible": 1,
    "divergent": 1,
    "excepted": 0,
    "fixed_upstream": 1,
    "unknown": 0
  },
  "results": [
    {
      "baseline_entry_id": "toolchain.rustc",
      "outcome": "compatible",
      "observed": "upstream UI suite passed"
    },
    {
      "baseline_entry_id": "toolchain.rustdoc",
      "outcome": "divergent",
      "observed": "stderr mismatch in tests/rustdoc/foo.rs"
    },
    {
      "baseline_entry_id": "toolchain.cargo",
      "outcome": "fixed_upstream",
      "observed": "upstream changed cargo invocation semantics",
      "upstream_fix_id": "fix.cargo.cli"
    }
  ]
}"#,
        )
        .expect("compat summary fixture should be writable");

        let (dimensions, ingest) =
            read_compat_summary(&path, false).expect("canonical summary should ingest");
        assert_eq!(ingest.rows, 3);
        assert_eq!(ingest.compatible, 1);
        assert_eq!(ingest.non_compatible, 2);
        assert_eq!(ingest.unknown, 0);
        assert!(dimensions.iter().any(|dimension| {
            dimension.id == "compat.toolchain.rustdoc"
                && dimension
                    .evidence
                    .iter()
                    .any(|item| item.contains("stderr mismatch in tests/rustdoc/foo.rs"))
        }));

        let report = evaluate_suite(
            Some("compat-summary".to_string()),
            EffectivePolicy::from_input(&PolicyInput::default()),
            dimensions,
            Some(ingest),
        );
        let blocker = report
            .blockers
            .iter()
            .find(|blocker| {
                blocker.dimension_id.as_deref() == Some("compat.toolchain.rustdoc")
                    && blocker.kind == BlockerKind::CompatibilityNotProven
            })
            .expect("divergent compatibility row should become an actionable blocker");
        assert!(blocker.action.contains("stderr mismatch in tests/rustdoc/foo.rs"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_requires_provenance() {
        let root = temp_repo_root("compat-summary-missing-provenance");
        let path = root.join("summary.json");
        fs::write(
            &path,
            r#"{
  "schema_version": "0.1.0",
  "baseline_id": "baseline.cli",
  "generated_on": "2026-04-26",
  "totals": {
    "total": 1,
    "compatible": 1,
    "divergent": 0,
    "excepted": 0,
    "fixed_upstream": 0,
    "unknown": 0
  },
  "results": [
    {
      "baseline_entry_id": "toolchain.rustc",
      "outcome": "compatible",
      "observed": "upstream UI suite passed"
    }
  ]
}"#,
        )
        .expect("compat summary fixture should be writable");

        let error =
            read_compat_summary(&path, false).expect_err("missing provenance should fail closed");
        let message = error.to_string();
        assert!(message.contains("proof-grade provenance"));
        assert!(message.contains("repo_head"));
        assert!(message.contains("runner"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_missing_declared_totals() {
        let root = temp_repo_root("compat-summary-missing-totals");
        let path = root.join("summary.json");
        let mut summary = compatibility_summary_report_with_runner(rust_upstream_compat_runner());
        summary.as_object_mut().expect("summary object").remove("totals");
        write_json(&path, &summary);

        let error =
            read_compat_summary(&path, false).expect_err("missing totals should fail closed");
        assert!(error.to_string().contains("must declare totals"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_dirty_repo_provenance() {
        let root = temp_repo_root("compat-summary-dirty-repo");
        let path = root.join("summary.json");
        let mut summary = compatibility_summary_report_with_runner(rust_upstream_compat_runner());
        summary["repo_dirty"] = serde_json::json!(true);
        write_json(&path, &summary);

        let error =
            read_compat_summary(&path, false).expect_err("dirty summary should fail closed");
        assert!(error.to_string().contains("repo_dirty must be false"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_short_repo_head() {
        let root = temp_repo_root("compat-summary-short-head");
        let path = root.join("summary.json");
        let mut summary = compatibility_summary_report_with_runner(rust_upstream_compat_runner());
        summary["repo_head"] = serde_json::json!("0123456");
        write_json(&path, &summary);

        let error =
            read_compat_summary(&path, false).expect_err("short repo head should fail closed");
        assert!(error.to_string().contains("repo_head must be a full git SHA"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_weak_upstream_revision() {
        let root = temp_repo_root("compat-summary-weak-upstream-revision");
        let path = root.join("summary.json");
        let mut summary = compatibility_summary_report_with_runner(rust_upstream_compat_runner());
        summary["upstream_revision"] = serde_json::json!("rust-lang/rust:main");
        write_json(&path, &summary);

        let error =
            read_compat_summary(&path, false).expect_err("weak upstream revision should fail");
        assert!(error.to_string().contains("upstream_revision must include a full git SHA"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_nested_python_runner_argv() {
        let root = temp_repo_root("compat-summary-python-runner-argv");
        let path = root.join("summary.json");
        let summary = compatibility_summary_report_with_runner(serde_json::json!({
            "implementation": "rust",
            "python_used": false,
            "command": {
                "argv": [
                    "python3",
                    "scripts/run_trust_upstream.py",
                    "targo",
                    "trust",
                    "domination",
                    "upstream-tests"
                ]
            }
        }));
        write_json(&path, &summary);

        let error =
            read_compat_summary(&path, false).expect_err("nested Python argv should fail closed");
        assert!(error.to_string().contains("runner must declare python_used=false"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_non_rust_runner_identity() {
        let root = temp_repo_root("compat-summary-non-rust-runner");
        let path = root.join("summary.json");
        let summary = compatibility_summary_report_with_runner(serde_json::json!({
            "implementation": "go",
            "python_used": false,
            "entrypoint": "targo trust domination upstream-tests"
        }));
        write_json(&path, &summary);

        let error =
            read_compat_summary(&path, false).expect_err("non-Rust runner should fail closed");
        assert!(error.to_string().contains("Rust-owned trust-upstream-compat entrypoint"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_weak_runner_identity() {
        let root = temp_repo_root("compat-summary-weak-runner");
        let path = root.join("summary.json");
        let summary = compatibility_summary_report_with_runner(serde_json::json!({
            "implementation": "rust",
            "python_used": false,
            "tool": "trust-upstream-compat",
            "note": "targo trust domination upstream-tests"
        }));
        write_json(&path, &summary);

        let error =
            read_compat_summary(&path, false).expect_err("weak runner identity should fail closed");
        assert!(error.to_string().contains("Rust-owned trust-upstream-compat entrypoint"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_requires_release_argv_provenance() {
        let root = temp_repo_root("compat-summary-missing-release-argv");
        let path = root.join("summary.json");
        let summary = compatibility_summary_report_with_runner(serde_json::json!({
            "implementation": "rust",
            "entrypoint": "targo trust domination upstream-tests",
            "python_used": false,
            "tool": "trust-upstream-compat"
        }));
        write_json(&path, &summary);

        let error =
            read_compat_summary(&path, false).expect_err("weak release argv should fail closed");
        let message = error.to_string();
        assert!(message.contains("release argv"));
        assert!(message.contains("--release --proof-mode full --execute --summary-out"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_bounded_release_argv() {
        let root = temp_repo_root("compat-summary-bounded-release-argv");
        let path = root.join("summary.json");
        let mut runner = rust_upstream_compat_runner();
        runner["argv"]
            .as_array_mut()
            .expect("runner argv")
            .extend([serde_json::json!("--max-files"), serde_json::json!("1")]);
        let summary = compatibility_summary_report_with_runner(runner);
        write_json(&path, &summary);

        let error =
            read_compat_summary(&path, false).expect_err("bounded release argv should fail closed");
        assert!(error.to_string().contains("release argv"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_mismatched_declared_totals() {
        let root = temp_repo_root("compat-summary-bad-totals");
        let path = root.join("summary.json");
        fs::write(
            &path,
            r#"{
  "schema_version": "0.1.0",
  "baseline_id": "baseline.cli",
  "generated_on": "2026-04-26",
  "run_id": "ci-42",
  "repo_head": "0123456789abcdef0123456789abcdef01234567",
  "repo_dirty": false,
  "upstream_revision": "rust-lang/rust:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "runner": {
    "implementation": "rust",
    "entrypoint": "targo trust domination upstream-tests",
    "argv": ["targo", "trust", "domination", "upstream-tests", "--release", "--proof-mode", "full", "--execute", "--summary-out", "reports/upstream-rust/summary.json"],
    "release_evidence_contract": {
      "entrypoint": "targo trust domination upstream-tests",
      "release": true,
      "execute": true,
      "proof_mode": "full",
      "summary_out": "reports/upstream-rust/summary.json",
      "requires_release": true,
      "requires_execute": true,
      "requires_proof_mode": "full",
      "requires_summary_out": true,
      "satisfied": true
    },
    "python_used": false,
    "tool": "trust-upstream-compat"
  },
  "totals": {
    "total": 99,
    "compatible": 1,
    "divergent": 0,
    "excepted": 0,
    "fixed_upstream": 0,
    "unknown": 0
  },
  "results": [
    {
      "baseline_entry_id": "toolchain.rustc",
      "outcome": "compatible",
      "observed": "upstream UI suite passed"
    }
  ]
}"#,
        )
        .expect("compat summary fixture should be writable");

        let error =
            read_compat_summary(&path, false).expect_err("mismatched totals should fail closed");
        let message = error.to_string();
        assert!(message.contains("declares totals"));
        assert!(message.contains("computed"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_ingestion_rejects_unsupported_schema_version() {
        let root = temp_repo_root("compat-summary-bad-schema");
        let path = root.join("summary.json");
        fs::write(
            &path,
            r#"{
  "schema_version": "0.0.9",
  "baseline_id": "baseline.x86_64-linux",
  "generated_on": "2026-04-26",
  "run_id": "ci-42",
  "repo_head": "0123456789abcdef0123456789abcdef01234567",
  "repo_dirty": false,
  "upstream_revision": "rust-lang/rust:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "runner": {
    "implementation": "rust",
    "entrypoint": "targo trust domination upstream-tests",
    "argv": ["targo", "trust", "domination", "upstream-tests", "--release", "--proof-mode", "full", "--execute", "--summary-out", "reports/upstream-rust/summary.json"],
    "release_evidence_contract": {
      "entrypoint": "targo trust domination upstream-tests",
      "release": true,
      "execute": true,
      "proof_mode": "full",
      "summary_out": "reports/upstream-rust/summary.json",
      "requires_release": true,
      "requires_execute": true,
      "requires_proof_mode": "full",
      "requires_summary_out": true,
      "satisfied": true
    },
    "python_used": false,
    "tool": "trust-upstream-compat"
  },
  "target_arch": "x86_64",
  "totals": {
    "total": 1,
    "compatible": 1,
    "divergent": 0,
    "excepted": 0,
    "fixed_upstream": 0,
    "unknown": 0
  },
  "results": [
    {
      "baseline_entry_id": "toolchain.rustc",
      "outcome": "compatible",
      "observed": "upstream UI suite passed"
    }
  ]
}"#,
        )
        .expect("compat summary fixture should be writable");

        let error = read_compat_summary(&path, false).expect_err("stale schema should fail closed");
        let message = error.to_string();
        assert!(message.contains("schema_version"));
        assert!(message.contains(UPSTREAM_COMPAT_SUMMARY_SCHEMA_VERSION));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn compat_summary_target_arch_aggregates_default_launch_dimension() {
        let root = temp_repo_root("compat-summary-target-arch");
        let path = root.join("summary.json");
        fs::write(
            &path,
            r#"{
  "schema_version": "0.1.0",
  "baseline_id": "baseline.x86_64-linux",
  "generated_on": "2026-04-26",
  "run_id": "ci-42",
  "repo_head": "0123456789abcdef0123456789abcdef01234567",
  "repo_dirty": false,
  "upstream_revision": "rust-lang/rust:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "runner": {
    "implementation": "rust",
    "entrypoint": "targo trust domination upstream-tests",
    "argv": ["targo", "trust", "domination", "upstream-tests", "--release", "--proof-mode", "full", "--execute", "--summary-out", "reports/upstream-rust/summary.json"],
    "release_evidence_contract": {
      "entrypoint": "targo trust domination upstream-tests",
      "release": true,
      "execute": true,
      "proof_mode": "full",
      "summary_out": "reports/upstream-rust/summary.json",
      "requires_release": true,
      "requires_execute": true,
      "requires_proof_mode": "full",
      "requires_summary_out": true,
      "satisfied": true
    },
    "python_used": false,
    "tool": "trust-upstream-compat"
  },
  "target_arch": "x86_64",
  "totals": {
    "total": 2,
    "compatible": 2,
    "divergent": 0,
    "excepted": 0,
    "fixed_upstream": 0,
    "unknown": 0
  },
  "results": [
    {
      "baseline_entry_id": "toolchain.rustc",
      "outcome": "compatible",
      "observed": "upstream UI suite passed"
    },
    {
      "baseline_entry_id": "toolchain.rustdoc",
      "outcome": "compatible",
      "observed": "upstream rustdoc suite passed"
    }
  ]
}"#,
        )
        .expect("compat summary fixture should be writable");

        let (compat_dimensions, ingest) =
            read_compat_summary(&path, false).expect("target summary should ingest");
        assert_eq!(ingest.compatible, 2);
        assert!(compat_dimensions.iter().any(|dimension| {
            dimension.id == "compat.x86_64.toolchain"
                && dimension.status == Some(DeclaredStatus::Pass)
                && dimension.evidence.iter().any(|item| item.contains("target_arch=x86_64"))
        }));

        let mut dimensions = default_launch_dimensions();
        for dimension in compat_dimensions {
            upsert_dimension(&mut dimensions, dimension);
        }
        let report = evaluate_suite(
            Some("compat-aggregate".to_string()),
            EffectivePolicy::from_input(&PolicyInput::default()),
            dimensions,
            Some(ingest),
        );
        let x86 = report
            .dimensions
            .iter()
            .find(|dimension| dimension.id == "compat.x86_64.toolchain")
            .expect("x86 compat aggregate");
        assert_eq!(x86.status, DimensionStatus::Pass);
        assert_eq!(
            report
                .dimensions
                .iter()
                .filter(|dimension| dimension.id == "compat.x86_64.toolchain")
                .count(),
            1
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_classifies_binary_roundtrip_dimension() {
        let root = temp_repo_root("product-proof-release-pass");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should ingest");
        assert_eq!(dimension.id, PRODUCT_PROOF_BINARY_ROUNDTRIP_DIMENSION_ID);
        assert_eq!(dimension.status, Some(DeclaredStatus::Pass));
        assert_eq!(dimension.rust_value, Some(0.0));
        assert_eq!(dimension.trust_value, Some(1.0));

        let report = suite_with(vec![dimension]);
        assert_eq!(report.dimensions[0].status, DimensionStatus::Pass);
        assert!(report.dimensions[0].trust_is_better);

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_resolves_repo_root_evidence_refs() {
        let root = temp_repo_root("product-proof-release-repo-root-ref");
        let path = root.join("reports/release/release-report.json");
        fs::create_dir_all(path.parent().expect("report parent")).expect("report dir");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report["repo_root"] = serde_json::json!(root.display().to_string());
        write_json(&path, &report);

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should ingest");

        assert_eq!(dimension.status, Some(DeclaredStatus::Pass));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_oversized_input_before_parsing() {
        let root = temp_repo_root("product-proof-release-oversized");
        let path = root.join("release-report.json");
        let file = fs::File::create(&path).expect("oversized report fixture");
        file.set_len(MAX_RELEASE_TRANSCRIPT_REPORT_BYTES as u64 + 1).expect("extend sparse report");

        let error = read_product_proof_release_report(&path)
            .expect_err("oversized release report must fail closed");

        assert!(format!("{error:#}").contains("safety limit"));
        let _ = fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn product_proof_release_report_rejects_leaf_symlink_input() {
        use std::os::unix::fs::symlink;

        let root = temp_repo_root("product-proof-release-symlink-report");
        let target = root.join("target.json");
        let linked = root.join("release-report.json");
        write_json(&target, &product_proof_release_report(Vec::new()));
        symlink(&target, &linked).expect("release report symlink fixture");

        let error = read_product_proof_release_report(&linked)
            .expect_err("symlinked release report must fail closed");

        assert!(format!("{error:#}").contains("not a regular file"));
        let _ = fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn product_proof_evidence_resolution_rejects_symlink_component() {
        use std::os::unix::fs::symlink;

        let root = temp_repo_root("product-proof-evidence-symlink-component");
        let outside = temp_repo_root("product-proof-evidence-symlink-outside");
        symlink(&outside, root.join("release")).expect("evidence directory symlink fixture");

        let error = resolve_product_proof_evidence_path(&root, "release/evidence/proof.json")
            .expect_err("symlinked evidence component must fail closed");

        assert!(error.to_string().contains("is a symlink"));
        let _ = fs::remove_dir_all(root);
        let _ = fs::remove_dir_all(outside);
    }

    #[test]
    fn product_proof_release_repo_root_rejects_relative_traversal() {
        let root = temp_repo_root("product-proof-release-root-traversal");
        let path = root.join("reports/release-report.json");
        fs::create_dir_all(path.parent().expect("report parent")).expect("report directory");
        let report = serde_json::json!({ "repo_root": "../outside" });

        let error = product_proof_release_repo_root(&path, &report)
            .expect_err("relative repo_root traversal must fail closed");

        assert!(error.to_string().contains("not a contained path"));
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_private_visibility() {
        let root = temp_repo_root("product-proof-release-private");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report["visibility"] = serde_json::json!("private");
        write_json(&path, &report);

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(
            dimension
                .ai_hint
                .as_deref()
                .is_some_and(|hint| hint.contains("visibility must be public"))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_missing_release_evidence_semantics() {
        let root = temp_repo_root("product-proof-release-missing-evidence-semantics");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        let object = report.as_object_mut().expect("release report object");
        object.remove("evidence_mode");
        object.remove("release_evidence");

        assert_product_proof_release_report_fails_with_hint(
            &root,
            "release-report",
            report,
            &[
                "evidence_mode must be golden-path",
                "structured release_evidence golden-path semantics",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_diagnostic_only_release_evidence_semantics() {
        let root = temp_repo_root("product-proof-release-diagnostic-only-evidence");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report["evidence_mode"] = serde_json::json!("diagnostic-only");
        report["release_evidence"] = serde_json::json!({
            "claim": "diagnostic-only",
            "golden_path": false,
            "reason": "metadata/private diagnostics are not release evidence"
        });

        assert_product_proof_release_report_fails_with_hint(
            &root,
            "release-report",
            report,
            &[
                "evidence_mode must be golden-path",
                "release_evidence.claim must be golden-path",
                "release_evidence.golden_path must be true",
            ],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_false_golden_path_release_evidence() {
        let root = temp_repo_root("product-proof-release-false-golden-path");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report["release_evidence"]["golden_path"] = serde_json::json!(false);

        assert_product_proof_release_report_fails_with_hint(
            &root,
            "release-report",
            report,
            &["release_evidence.golden_path must be true"],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_dirty_repo_provenance() {
        let root = temp_repo_root("product-proof-release-dirty-repo");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report["repo_dirty"] = serde_json::json!(true);
        write_json(&path, &report);

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(
            dimension
                .ai_hint
                .as_deref()
                .is_some_and(|hint| hint.contains("repo_dirty must be false"))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_missing_repo_dirty_provenance() {
        let root = temp_repo_root("product-proof-release-missing-repo-dirty");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report.as_object_mut().expect("release report object").remove("repo_dirty");
        write_json(&path, &report);

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| hint.contains("repo_dirty=false")));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_requires_proof_grade_dirty_metadata() {
        let root = temp_repo_root("product-proof-release-weak-dirty-metadata");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report["repo_dirty_metadata"]["untracked_files"] = serde_json::json!("included");
        report["repo_dirty_metadata"]
            .as_object_mut()
            .expect("metadata object")
            .remove("ignore_submodules");

        assert_product_proof_release_report_fails_with_hint(
            &root,
            "release-report",
            report,
            &["untracked_files must be all", "ignore_submodules=none"],
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_missing_runner_provenance() {
        let root = temp_repo_root("product-proof-release-missing-runner");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report.as_object_mut().expect("release report object").remove("runner");
        write_json(&path, &report);

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(
            dimension
                .ai_hint
                .as_deref()
                .is_some_and(|hint| hint.contains("structured runner identity"))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_nested_python_runner_argv() {
        let root = temp_repo_root("product-proof-release-python-runner-argv");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report["runner"] = serde_json::json!({
            "implementation": "rust",
            "python_used": false,
            "command": {
                "argv": [
                    "python3",
                    "release/product-proof.py",
                    "targo",
                    "trust",
                    "release",
                    "check"
                ]
            }
        });
        write_json(&path, &report);

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("runner must declare python_used=false")
                && hint.contains("targo trust release check")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_non_rust_runner_identity() {
        let root = temp_repo_root("product-proof-release-non-rust-runner");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report["runner"] = serde_json::json!({
            "implementation": "go",
            "python_used": false,
            "entrypoint": "targo trust release check"
        });
        write_json(&path, &report);

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("Rust-owned targo trust release check entrypoint")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_weak_runner_identity() {
        let root = temp_repo_root("product-proof-release-weak-runner");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut report = product_proof_release_report(evidence_refs);
        report["runner"] = serde_json::json!({
            "implementation": "rust",
            "python_used": false,
            "tool": "targo-trust",
            "note": "targo trust release check"
        });
        write_json(&path, &report);

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("Rust-owned targo trust release check entrypoint")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_missing_compile_back_ref_fails_closed() {
        let root = temp_repo_root("product-proof-release-missing-ref");
        let path = root.join("release-report.json");
        let mut evidence_refs = write_product_proof_compile_back_evidence(&root);
        evidence_refs.remove(0);
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");
        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("compile-back-artifact-digests-bound") && hint.contains("product-proof")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_missing_required_compile_back_declaration_fails_closed() {
        let root = temp_repo_root("product-proof-release-missing-required-declaration");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        write_json(
            &path,
            &product_proof_release_report_with_required_evidence(
                evidence_refs,
                COMPILE_BACK_REQUIRED_EVIDENCE.iter().copied().skip(1).collect(),
            ),
        );

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("binary/decomp gates component required_evidence")
                && hint.contains("compile-back-artifact-digests-bound")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_missing_compile_back_total_fails_closed() {
        let root = temp_repo_root("product-proof-release-missing-proof-total");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-artifact-digests-bound");
        evidence["proof_results"].as_object_mut().expect("proof_results object").remove("total");
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-artifact-digests-bound")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(
            dimension
                .ai_hint
                .as_deref()
                .is_some_and(|hint| hint.contains("proof_results.total must be declared"))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_compile_back_python_runner() {
        let root = temp_repo_root("product-proof-release-evidence-python-runner");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-artifact-digests-bound");
        evidence["runner"] = serde_json::json!({
            "implementation": "rust",
            "python_used": false,
            "command": {
                "argv": [
                    "/usr/bin/env",
                    "python3",
                    "release/product-proof.py",
                    "targo",
                    "trust",
                    "release",
                    "check"
                ]
            }
        });
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-artifact-digests-bound")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("compile-back-artifact-digests-bound")
                && hint.contains("runner must declare python_used=false")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_accepts_verify_binary_compile_back_runner() {
        let root = temp_repo_root("product-proof-release-verify-binary-runner");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-artifact-digests-bound");
        evidence["runner"] = serde_json::json!({
            "implementation": "rust",
            "entrypoint": "targo trust verify-binary",
            "python_used": false,
            "tool": "targo-trust"
        });
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-artifact-digests-bound")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Pass));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_weak_compile_back_runner_identity() {
        let root = temp_repo_root("product-proof-release-weak-evidence-runner");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-artifact-digests-bound");
        evidence["runner"] = serde_json::json!({
            "implementation": "rust",
            "python_used": false,
            "tool": "targo-trust",
            "note": "targo trust verify-binary"
        });
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-artifact-digests-bound")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("compile-back-artifact-digests-bound")
                && hint.contains("Rust-owned Trust product-proof tooling")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_unstamped_compile_back_evidence() {
        let root = temp_repo_root("product-proof-release-unstamped-evidence");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-artifact-digests-bound");
        evidence.as_object_mut().expect("evidence object").remove("generated_at");
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-artifact-digests-bound")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(
            dimension
                .ai_hint
                .as_deref()
                .is_some_and(|hint| hint.contains("generated_at/checked_at"))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_weak_compile_back_solver_identity() {
        let root = temp_repo_root("product-proof-release-weak-solver");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-artifact-digests-bound");
        evidence["proof_results"]["by_solver"] = serde_json::json!([" fake solver "]);
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-artifact-digests-bound")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| hint.contains("valid by_solver")));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_rejects_compile_back_without_solver_attribution() {
        let root = temp_repo_root("product-proof-release-missing-solver");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-artifact-digests-bound");
        evidence["proof_results"]
            .as_object_mut()
            .expect("proof_results object")
            .remove("by_solver");
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-artifact-digests-bound")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(
            dimension.ai_hint.as_deref().is_some_and(|hint| hint.contains("by_solver attribution"))
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_bare_compile_back_ref_fails_closed() {
        let root = temp_repo_root("product-proof-release-bare-ref");
        let path = root.join("release-report.json");
        let evidence_refs =
            COMPILE_BACK_REQUIRED_EVIDENCE.iter().map(|kind| kind.to_string()).collect();
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("product-proof-coverage evidence_refs")
                && hint.contains("compile-back-artifact-digests-bound:<path>")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_unmaterialized_compile_back_ref_fails_closed() {
        let root = temp_repo_root("product-proof-release-unmaterialized-ref");
        let path = root.join("release-report.json");
        let evidence_refs = COMPILE_BACK_REQUIRED_EVIDENCE
            .iter()
            .map(|kind| format!("{kind}:{}", compile_back_evidence_path_text(kind)))
            .collect();
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("could not reopen")
                && hint.contains("compile-back-artifact-digests-bound")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_stale_compile_back_schema_fails_closed() {
        let root = temp_repo_root("product-proof-release-stale-evidence-schema");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-artifact-digests-bound");
        evidence["schema_version"] = serde_json::json!("trust.product-proof.v0");
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-artifact-digests-bound")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("schema_version") && hint.contains(PRODUCT_PROOF_EVIDENCE_SCHEMA)
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_candidate_mismatch_fails_closed() {
        let root = temp_repo_root("product-proof-release-candidate-mismatch");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-rust-source-sha256");
        evidence["candidate_commit"] =
            serde_json::json!("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-rust-source-sha256")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("candidate_commit") && hint.contains("compile-back-rust-source-sha256")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_conflicting_compile_back_digest_fails_closed() {
        let root = temp_repo_root("product-proof-release-conflicting-digest");
        let path = root.join("release-report.json");
        let evidence_refs = write_product_proof_compile_back_evidence(&root);
        let mut evidence =
            product_proof_compile_back_evidence(&root, "compile-back-root-artifact-sha256");
        evidence["compile_back_artifact_digest_binding"]["root_artifact_sha256"] =
            serde_json::json!("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        write_json(
            &root.join(compile_back_evidence_path_text("compile-back-root-artifact-sha256")),
            &evidence,
        );
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Fail));
        assert!(dimension.ai_hint.as_deref().is_some_and(|hint| {
            hint.contains("root_artifact_sha256") && hint.contains("conflicting")
        }));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn product_proof_release_report_normalizes_prefixed_digest_whitespace() {
        let root = temp_repo_root("product-proof-release-digest-whitespace");
        let path = root.join("release-report.json");
        fs::create_dir_all(root.join("release/evidence")).expect("evidence dir should be created");
        let evidence_refs = COMPILE_BACK_REQUIRED_EVIDENCE
            .iter()
            .map(|required| {
                let path_text = compile_back_evidence_path_text(required);
                let mut evidence = product_proof_compile_back_evidence(&root, required);
                let binding = evidence["compile_back_artifact_digest_binding"]
                    .as_object_mut()
                    .expect("binding object");
                for key in [
                    "lifted_binary_trust_ir_sha256",
                    "rust_source_sha256",
                    "reconstructed_trust_ir_sha256",
                    "refinement_artifact_sha256",
                    "root_artifact_sha256",
                    "selected_image_sha256",
                ] {
                    if let Some(value) =
                        binding.get(key).and_then(Value::as_str).map(str::to_string)
                    {
                        binding.insert(
                            key.to_string(),
                            serde_json::json!(format!(" sha256:{value} ")),
                        );
                    }
                }
                write_json(&root.join(&path_text), &evidence);
                format!("{required}:{path_text}")
            })
            .collect();
        write_json(&path, &product_proof_release_report(evidence_refs));

        let dimension =
            read_product_proof_release_report(&path).expect("product-proof report should parse");

        assert_eq!(dimension.status, Some(DeclaredStatus::Pass));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn parser_accepts_template_format_flag() {
        let args = parse_args(&[
            "--write-template".to_string(),
            "-".to_string(),
            "--format=json".to_string(),
            "--compat-summary=reports/upstream-rust/aarch64/summary.json".to_string(),
            "--compat-summary".to_string(),
            "reports/upstream-rust/x86_64/summary.json".to_string(),
            "--proof-program-index-report=reports/bench/program-index/proof-functional/report.json"
                .to_string(),
            "--proof-unsafe-memory-report=reports/proof/unsafe-memory.json".to_string(),
            "--proof-concurrency-report".to_string(),
            "reports/proof/concurrency.json".to_string(),
            "--program-index-benchmark-report=reports/bench/program-index/cold/report.json"
                .to_string(),
            "--program-index-benchmark-report".to_string(),
            "reports/bench/program-index/warm/report.json".to_string(),
            "--product-proof-release-report=reports/release/product-proof.json".to_string(),
        ])
        .expect("template args should parse");

        assert_eq!(args.write_template, Some(PathBuf::from("-")));
        assert_eq!(args.format, OutputFormat::Json);
        assert_eq!(
            args.proof_program_index_report,
            Some(PathBuf::from("reports/bench/program-index/proof-functional/report.json"))
        );
        assert_eq!(
            args.proof_unsafe_memory_report,
            Some(PathBuf::from("reports/proof/unsafe-memory.json"))
        );
        assert_eq!(
            args.proof_concurrency_report,
            Some(PathBuf::from("reports/proof/concurrency.json"))
        );
        assert_eq!(
            args.compat_summary,
            vec![
                PathBuf::from("reports/upstream-rust/aarch64/summary.json"),
                PathBuf::from("reports/upstream-rust/x86_64/summary.json"),
            ]
        );
        assert_eq!(
            args.program_index_benchmark_report,
            vec![
                PathBuf::from("reports/bench/program-index/cold/report.json"),
                PathBuf::from("reports/bench/program-index/warm/report.json"),
            ]
        );
        assert_eq!(
            args.product_proof_release_report,
            Some(PathBuf::from("reports/release/product-proof.json"))
        );
    }

    #[test]
    fn template_uses_current_schema() {
        assert!(TEMPLATE.contains(SUITE_SCHEMA_VERSION));
    }

    #[test]
    fn template_pins_proof_functional_program_index_gate() {
        assert!(TEMPLATE.contains(PROOF_FUNCTIONAL_DIMENSION_ID));
        assert!(TEMPLATE.contains(PROOF_FUNCTIONAL_EVIDENCE_COMMAND));
        assert!(TEMPLATE.contains(PROOF_FUNCTIONAL_REPORT_FLAG));
        assert!(TEMPLATE.contains(PROGRAM_INDEX_REPORT_SCHEMA));
        assert!(TEMPLATE.contains("status = \"unknown\""));
        assert!(TEMPLATE.contains("evidence = []"));
    }

    #[test]
    fn template_pins_proof_unsafe_memory_report_gate() {
        assert!(TEMPLATE.contains(PROOF_UNSAFE_MEMORY_DIMENSION_ID));
        assert!(TEMPLATE.contains(PROOF_UNSAFE_MEMORY_EVIDENCE_COMMAND));
        assert!(TEMPLATE.contains(PROOF_UNSAFE_MEMORY_REPORT_FLAG));
        assert!(TEMPLATE.contains(PROOF_UNSAFE_MEMORY_REPORT_SCHEMA));
    }

    #[test]
    fn template_pins_proof_concurrency_report_gate() {
        assert!(TEMPLATE.contains(PROOF_CONCURRENCY_DIMENSION_ID));
        assert!(PROOF_CONCURRENCY_EVIDENCE_COMMAND.starts_with("not implemented:"));
        assert!(TEMPLATE.contains("fail-closed until a Trust-owned authenticated validator"));
        assert!(TEMPLATE.contains(PROOF_CONCURRENCY_REPORT_FLAG));
        assert!(TEMPLATE.contains(PROOF_CONCURRENCY_REPORT_SCHEMA));
        assert!(TEMPLATE.contains("status = \"unknown\""));
        assert!(TEMPLATE.contains("evidence = []"));
    }

    #[test]
    fn domination_help_pins_upstream_tests_to_rust_porting_front_door() {
        let help = usage_text();
        assert!(help.contains("targo trust domination upstream-tests [port options]"));
        assert!(help.contains("Rust `trust-upstream-compat port` engine"));
        assert!(help.contains("Python is not used."));
        assert!(!help.contains("targo trust rust-vs-trust"));
        assert!(!help.contains("upstream-rust-tests"));

        let upstream_help = upstream_tests_usage_text();
        assert!(upstream_help.contains("targo trust domination upstream-tests"));
        assert!(upstream_help.contains("Rust `trust-upstream-compat port` command"));
        assert!(upstream_help.contains("Python is not used."));
        assert!(!upstream_help.contains("upstream-rust-tests"));
    }

    #[test]
    fn rust_vs_trust_upstream_tests_canonical_dispatches_to_rust_porting_command() {
        assert!(is_upstream_tests_subcommand("upstream-tests"));
        assert!(!is_upstream_tests_subcommand("upstream-rust-tests"));

        let help_args = vec!["upstream-tests".to_string(), "--help".to_string()];
        assert_eq!(run_subcommand(&help_args), ExitCode::SUCCESS);

        let removed_alias_args = vec!["upstream-rust-tests".to_string(), "--help".to_string()];
        assert_eq!(run_subcommand(&removed_alias_args), ExitCode::from(2));

        let port_args =
            vec!["--execute".to_string(), "--max-files=1".to_string(), "--release".to_string()];
        assert!(upstream_tests_requires_trust_cargo(&port_args));

        let preflight = build_upstream_compat_lockfile_preflight_command(
            vec!["targo".to_string()],
            Path::new("/repo"),
        );
        assert_eq!(preflight[0], "targo");
        assert_eq!(preflight[1], "metadata");
        assert_eq!(preflight[2], "--manifest-path");
        assert_eq!(preflight[3], "/repo/crates/trust-upstream-compat/Cargo.toml");
        assert_eq!(preflight[4], "--locked");
        assert_eq!(preflight[5], "--format-version");
        assert_eq!(preflight[6], "1");
        assert_eq!(preflight[7], "--no-deps");

        let command =
            build_upstream_tests_command(vec!["targo".to_string()], Path::new("/repo"), &port_args);

        assert_eq!(command[0], "targo");
        assert_eq!(command[1], "run");
        assert_eq!(command[2], "--manifest-path");
        assert_eq!(command[3], "/repo/crates/trust-upstream-compat/Cargo.toml");
        assert_eq!(command[4], "--locked");
        assert_eq!(command[5], "--");
        assert_eq!(command[6], "port");
        assert_eq!(&command[7..], port_args.as_slice());
        assert!(command.iter().all(|part| !part.to_ascii_lowercase().contains("python")));
        assert!(preflight.iter().all(|part| !part.to_ascii_lowercase().contains("python")));
    }

    #[test]
    #[cfg(unix)]
    fn rust_vs_trust_upstream_tests_preflight_reports_locked_manifest_failures() {
        use std::os::unix::fs::PermissionsExt;

        let root = temp_repo_root("locked-preflight-failure");
        let targo = root.join("bin/targo");
        fs::create_dir_all(targo.parent().expect("fake targo should have parent"))
            .expect("fake targo parent should be creatable");
        fs::write(&targo, "#!/bin/sh\necho 'Cargo.lock needs to be updated' >&2\nexit 101\n")
            .expect("fake targo should be writable");
        let mut permissions = fs::metadata(&targo).expect("fake targo metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&targo, permissions).expect("fake targo should become executable");

        let error =
            preflight_upstream_compat_lockfile(&[targo.to_string_lossy().into_owned()], &root)
                .expect_err("stale lockfile preflight must fail before porting");
        let message = error.to_string();

        assert!(message.contains("preflight failed under --locked before porting"));
        assert!(message.contains("metadata --manifest-path"));
        assert!(message.contains("Cargo.lock needs to be updated"));
        assert!(message.contains("targo update --manifest-path"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rust_vs_trust_upstream_tests_repo_root_prefers_active_git_checkout() {
        let root = temp_repo_root("active-git-root");
        fs::create_dir_all(root.join("crates/trust-upstream-compat"))
            .expect("upstream compat manifest parent should be creatable");
        fs::write(
            root.join("crates/trust-upstream-compat/Cargo.toml"),
            "[package]\nname = \"trust-upstream-compat\"\nversion = \"0.0.0\"\nedition = \"2021\"\n",
        )
        .expect("upstream compat manifest should be writable");
        let status = Command::new("git")
            .arg("-C")
            .arg(&root)
            .args(["-c", "init.defaultBranch=main", "init", "--quiet"])
            .status()
            .expect("git init should run");
        assert!(status.success(), "git init should succeed");
        let nested = root.join("nested/workdir");
        fs::create_dir_all(&nested).expect("nested test cwd should be creatable");

        let resolved =
            repo_root_from_git_or_manifest_with_cwd(&nested, Path::new("/manifest/fallback"))
                .expect("active checkout with upstream compat manifest should be accepted");

        assert_eq!(resolved, root.canonicalize().expect("test git root should canonicalize"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rust_vs_trust_upstream_tests_release_rejects_ambient_cargo_fallback() {
        let root = temp_repo_root("release-ambient-cargo");

        let error = resolve_upstream_compat_cargo_from_probe(
            &root,
            true,
            UpstreamCompatCargoProbe::default(),
        )
        .expect_err("release porting must reject ambient upstream cargo fallback");
        let message = error.to_string();

        assert!(message.contains("release upstream porting requires canonical Trust targo"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rust_vs_trust_upstream_tests_non_release_rejects_ambient_cargo_fallback() {
        let root = temp_repo_root("non-release-ambient-cargo");

        let error = resolve_upstream_compat_cargo_from_probe(
            &root,
            false,
            UpstreamCompatCargoProbe::default(),
        )
        .expect_err("developer porting must reject ambient upstream cargo fallback");
        let message = error.to_string();

        assert!(message.contains("developer upstream porting requires canonical Trust targo"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn rust_vs_trust_upstream_tests_release_rejects_configured_ambient_cargo() {
        let root = temp_repo_root("release-configured-cargo");

        let error = resolve_upstream_compat_cargo_from_probe(
            &root,
            true,
            UpstreamCompatCargoProbe {
                configured: Some("cargo".to_string()),
                ..Default::default()
            },
        )
        .expect_err("release porting must reject configured ambient upstream cargo");
        let message = error.to_string();

        assert!(message.contains("TRUST_UPSTREAM_COMPAT_CARGO"));
        assert!(message.contains("must name canonical targo"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    #[cfg(unix)]
    fn rust_vs_trust_upstream_tests_release_accepts_repo_stage2_targo() {
        let root = temp_repo_root("release-stage2-targo");
        let head = init_git_head(&root);
        let stage2_targo = write_fake_stage2_targo(&root, "host", &head);

        let driver = resolve_upstream_compat_cargo_from_probe(
            &root,
            true,
            UpstreamCompatCargoProbe {
                repo_stage2_targo: Some(stage2_targo.clone()),
                ..Default::default()
            },
        )
        .expect("repo stage2 targo should satisfy release porting");

        let exported_cargo = upstream_compat_child_cargo_env(&driver);
        let port_args = vec!["--release".to_string()];
        let command = build_upstream_tests_command(driver, &root, &port_args);

        assert_eq!(command[0], stage2_targo.to_string_lossy().into_owned());
        assert_eq!(command.last().map(String::as_str), Some("--release"));
        assert_eq!(
            exported_cargo.as_deref(),
            Some(stage2_targo.to_string_lossy().as_ref()),
            "outer targo driver must be exported so trust-upstream-compat does not fall back to ambient Cargo"
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    #[cfg(unix)]
    fn rust_vs_trust_upstream_tests_release_discovers_custom_host_stage2_targo() {
        let root = temp_repo_root("release-custom-host-stage2-targo");
        let head = init_git_head(&root);
        let stage2_targo = write_fake_stage2_targo(&root, "custom-audit-host", &head);

        let discovered = find_repo_stage2_targo(&root)
            .expect("custom build/<host>/stage2 targo should be found");
        assert_eq!(discovered, stage2_targo);

        let driver = resolve_upstream_compat_cargo_from_probe(
            &root,
            true,
            UpstreamCompatCargoProbe { repo_stage2_targo: Some(discovered), ..Default::default() },
        )
        .expect("custom host stage2 targo should satisfy release porting");

        assert_eq!(driver[0], stage2_targo.to_string_lossy().into_owned());

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    #[cfg(unix)]
    fn rust_vs_trust_upstream_tests_release_rejects_stale_stage2_trustc() {
        let root = temp_repo_root("release-stale-stage2-trustc");
        let head = init_git_head(&root);
        let stale = "0000000000000000000000000000000000000000";
        assert_ne!(head, stale);
        let stage2_targo = write_fake_stage2_targo(&root, "host", stale);

        let error = resolve_upstream_compat_cargo_from_probe(
            &root,
            true,
            UpstreamCompatCargoProbe {
                repo_stage2_targo: Some(stage2_targo.clone()),
                ..Default::default()
            },
        )
        .expect_err("release porting must reject stale sibling trustc");
        let message = error.to_string();

        assert!(message.contains("refuses stale stage2 trustc"));
        assert!(message.contains(stale));
        assert!(message.contains(&head));
        assert!(message.contains("./x.py build --stage 2 compiler/rustc"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    #[cfg(unix)]
    fn rust_vs_trust_upstream_tests_release_rejects_non_executable_repo_stage2_targo() {
        let root = temp_repo_root("release-non-executable-stage2-targo");
        let stage2_targo = root.join("build/host/stage2/bin/targo");
        touch_file(&stage2_targo);

        let error = resolve_upstream_compat_cargo_from_probe(
            &root,
            true,
            UpstreamCompatCargoProbe {
                repo_stage2_targo: Some(stage2_targo.clone()),
                ..Default::default()
            },
        )
        .expect_err("release porting must reject non-executable repo-local targo");
        let message = error.to_string();

        assert!(message.contains("repo-local stage2 targo is not executable"));
        assert!(message.contains(&stage2_targo.to_string_lossy().to_string()));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    #[cfg(unix)]
    fn rust_vs_trust_upstream_tests_release_rejects_path_targo() {
        let root = temp_repo_root("release-path-targo");
        let targo = root.join("ambient/bin/targo");
        touch_executable_file(&targo);

        let error = resolve_upstream_compat_cargo_from_probe(
            &root,
            true,
            UpstreamCompatCargoProbe { path_targo: Some(targo.clone()), ..Default::default() },
        )
        .expect_err("release porting must reject PATH targo");
        let message = error.to_string();

        assert!(message.contains("release upstream porting requires repo-local stage2 targo"));
        assert!(message.contains(&targo.to_string_lossy().to_string()));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    #[cfg(unix)]
    fn rust_vs_trust_upstream_tests_rejects_non_executable_targo_override() {
        let root = temp_repo_root("non-executable-targo-override");
        let targo = root.join("custom/bin/targo");
        touch_file(&targo);

        let error = resolve_upstream_compat_cargo_from_probe(
            &root,
            false,
            UpstreamCompatCargoProbe {
                configured: Some(targo.to_string_lossy().into_owned()),
                ..Default::default()
            },
        )
        .expect_err("configured targo must be executable even for developer runs");
        let message = error.to_string();

        assert!(message.contains("TRUST_UPSTREAM_COMPAT_CARGO is not executable"));
        assert!(message.contains(&targo.to_string_lossy().to_string()));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn default_launch_rubric_prioritizes_aarch64_x86_and_strict_perf() {
        let dimensions = default_launch_dimensions();
        assert!(dimensions.iter().any(|dimension| dimension.id == "compat.aarch64.toolchain"));
        assert!(dimensions.iter().any(|dimension| dimension.id == "compat.x86_64.toolchain"));
        assert!(
            dimensions
                .iter()
                .filter(|dimension| dimension.category == DimensionCategory::Performance)
                .all(|dimension| dimension.min_trust_delta_pct == Some(0.000001))
        );
    }
}
