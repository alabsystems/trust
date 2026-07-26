//! Repeatable upstream Rust test porting workflow.
//!
//! This module is the Rust implementation of the upstream test re-import,
//! deterministic Trust adaptation, audit log, and scorecard workflow. The
//! public CLI surface is `targo trust domination upstream-tests`; the
//! `trust-upstream-compat port` binary subcommand is the engine entry point.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::Instant;

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    CompatibilityBaseline, CompatibilityOutcome, CompatibilityResult, CompatibilityResultSummary,
    CompatibilitySummaryRunner, ExceptionStatus, LocalFixAction, ParseError, ResultTotals,
    TestExceptionKind, TestExceptionLedger, TestInventory, TestInventoryEntry, TestKind,
    TestOutcome, TestProofBundle, TestProofTotals, TestResult, TestResultReport, TestSource,
    TrustAddedTestCommand, TrustAddedTestManifest, UpstreamFixLedger, UpstreamFixStatus,
    parse_baseline_json, parse_baseline_toml, parse_test_inventory_json,
    parse_test_result_report_json, parse_trust_added_tests_json, parse_trust_added_tests_toml,
    parse_upstream_fixes_json, parse_upstream_fixes_toml, validate_test_exceptions_for_date,
    validate_test_proof_bundle, validate_trust_added_tests,
};

const UPSTREAM_TEST_PREFIX: &str = "tests/";
const DEFAULT_REVIEWED_UPSTREAM_REVISION: &str =
    "rust-lang/rust:5e91de65d75d3c849c643f5079509b9e5985a5c0";
const LATEST_UPSTREAM_REVISION_REQUEST: &str = "rust-lang/rust:HEAD";
const DEFAULT_UPSTREAM_REMOTE: &str = "https://github.com/rust-lang/rust.git";
const PROOF_ARTIFACT_NAMES: [&str; 3] = ["inventory.json", "results.json", "proof-summary.json"];
const TRUST_ADDED_MANIFEST: &str = "tests/trust-added/manifest.toml";
const TRUST_ADDED_MANIFEST_ENV: &str = "TRUST_UPSTREAM_RUST_TRUST_ADDED_MANIFEST";
const PATCH_MANIFEST_SCHEMA_VERSION: &str = "0.1.0";
const PRIMARY_SUFFIXES: [&str; 2] = [".rs", ".js"];
const TEXT_SUFFIXES: [&str; 17] = [
    ".rs", ".err", ".stderr", ".stdout", ".fixed", ".md", ".js", ".css", ".html", ".json", ".toml",
    ".mir", ".diff", ".txt", ".svg", ".goml", ".ll",
];
const COMPILETEST_PREFIXES: [&str; 27] = [
    "tests/assembly/",
    "tests/assembly-llvm/",
    "tests/auxiliary/",
    "tests/build-std/",
    "tests/codegen/",
    "tests/codegen-llvm/",
    "tests/codegen-units/",
    "tests/coverage/",
    "tests/coverage-run-rustdoc/",
    "tests/crashes/",
    "tests/debuginfo/",
    "tests/incremental/",
    "tests/mir-opt/",
    "tests/pretty/",
    "tests/run-make-cargo/",
    "tests/run-make/",
    "tests/run-pass/",
    "tests/run-pass-valgrind/",
    "tests/rustdoc/",
    "tests/rustdoc-gui/",
    "tests/rustdoc-html/",
    "tests/rustdoc-json/",
    "tests/rustdoc-js/",
    "tests/rustdoc-js-std/",
    "tests/rustdoc-ui/",
    "tests/ui/",
    "tests/ui-fulldeps/",
];
const PENDING_LOCAL_FIX_ACTIONS: [LocalFixAction; 4] = [
    LocalFixAction::RebaseBaseline,
    LocalFixAction::CherryPick,
    LocalFixAction::PortFix,
    LocalFixAction::DropException,
];

/// Proof artifact requirement for upstream porting execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofMode {
    /// Full proof for unbounded imports, smoke proof for bounded imports.
    Auto,
    /// Smoke execution: score failures but do not require full proof artifacts.
    Smoke,
    /// Full execution: require complete proof artifacts for success.
    Full,
}

impl ProofMode {
    /// Parse a CLI proof mode.
    #[must_use]
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "auto" => Some(Self::Auto),
            "smoke" => Some(Self::Smoke),
            "full" => Some(Self::Full),
            _ => None,
        }
    }

    /// Resolve auto mode after knowing whether the import is bounded.
    #[must_use]
    pub fn resolved(self, max_files: Option<usize>) -> Self {
        match self {
            Self::Auto if max_files.is_some() => Self::Smoke,
            Self::Auto => Self::Full,
            mode => mode,
        }
    }

    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Smoke => "smoke",
            Self::Full => "full",
        }
    }
}

/// Options for the upstream test porting workflow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortOptions {
    pub repo_root: PathBuf,
    pub baseline: PathBuf,
    pub upstream_fixes: PathBuf,
    pub test_exceptions: Option<TestExceptionLedger>,
    pub patch_manifest: Option<PathBuf>,
    pub llm_directives: Option<PathBuf>,
    pub summary_out: Option<PathBuf>,
    pub run_id: Option<String>,
    pub target_arch: Option<String>,
    pub target: Option<String>,
    pub target_triple: Option<String>,
    pub host: Option<String>,
    pub host_triple: Option<String>,
    pub test_exception_validation_date: Option<String>,
    pub upstream_revision: String,
    pub upstream_remote: String,
    pub out_dir: PathBuf,
    pub execute: bool,
    pub apply: bool,
    pub fetch: bool,
    pub scorecard_log: Option<PathBuf>,
    pub bootstrap_args: String,
    pub max_files: Option<usize>,
    pub release: bool,
    pub proof_mode: ProofMode,
}

/// Terminal/report result from a porting run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortRunReport {
    pub exit_code: u8,
    pub requested_revision: String,
    pub requested_ref: String,
    pub upstream_remote: String,
    pub resolution_source: String,
    pub resolution_detail: String,
    pub resolved_revision: String,
    pub local_revision: String,
    pub imported_files: usize,
    pub upstream_test_files: usize,
    pub audit_records: usize,
    pub patch_records: usize,
    pub llm_directives_path: PathBuf,
    pub scorecard_path: PathBuf,
    pub compatibility_summary_path: PathBuf,
    pub failed_tests: u64,
    pub tool_failures: u64,
    pub validation_failures: Vec<Value>,
}

impl PortRunReport {
    #[must_use]
    pub fn render_terminal(&self, root: &Path) -> String {
        let mut output = String::new();
        pushln(
            &mut output,
            format_args!("Requested upstream revision: {}", self.requested_revision),
        );
        pushln(&mut output, format_args!("Requested upstream ref: {}", self.requested_ref));
        pushln(&mut output, format_args!("Upstream remote: {}", self.upstream_remote));
        pushln(
            &mut output,
            format_args!(
                "Resolution source: {} ({})",
                self.resolution_source, self.resolution_detail
            ),
        );
        pushln(&mut output, format_args!("Resolved upstream revision: {}", self.resolved_revision));
        pushln(&mut output, format_args!("Local repository revision: {}", self.local_revision));
        pushln(
            &mut output,
            format_args!(
                "Imported upstream test files: {} / {}",
                self.imported_files, self.upstream_test_files
            ),
        );
        pushln(&mut output, format_args!("Adapter audit records: {}", self.audit_records));
        pushln(&mut output, format_args!("Patch audit records: {}", self.patch_records));
        pushln(
            &mut output,
            format_args!("LLM directives: {}", display_path(&self.llm_directives_path, root)),
        );
        pushln(
            &mut output,
            format_args!("Scorecard: {}", display_path(&self.scorecard_path, root)),
        );
        pushln(
            &mut output,
            format_args!(
                "Compatibility summary: {}",
                display_path(&self.compatibility_summary_path, root)
            ),
        );
        pushln(&mut output, format_args!("Failed tests: {}", self.failed_tests));
        pushln(&mut output, format_args!("Tool build failures: {}", self.tool_failures));
        pushln(
            &mut output,
            format_args!("Validation failures: {}", self.validation_failures.len()),
        );
        for failure in &self.validation_failures {
            if let Some(object) = failure.as_object() {
                let kind = object.get("kind").and_then(Value::as_str).unwrap_or("validation");
                let message = object.get("message").and_then(Value::as_str).unwrap_or("");
                pushln(&mut output, format_args!("- {kind}: {message}"));
            }
        }
        output
    }
}

fn pushln(output: &mut String, args: std::fmt::Arguments<'_>) {
    use std::fmt::Write as _;
    let _ = output.write_fmt(args);
    output.push('\n');
}

/// Porting runtime error.
#[derive(Debug, Error)]
pub enum PortError {
    #[error("{0}")]
    Message(String),
    #[error("I/O error: {0}")]
    Io(#[from] io::Error),
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("accounting parse error: {0}")]
    Parse(#[from] ParseError),
    #[error("command failed ({status}): {command}\nstdout:\n{stdout}\nstderr:\n{stderr}")]
    CommandFailed { command: String, status: ExitStatus, stdout: String, stderr: String },
}

impl PortError {
    #[must_use]
    pub fn exit_code(&self) -> u8 {
        match self {
            Self::Message(_) | Self::CommandFailed { .. } => 2,
            Self::Io(_) | Self::Json(_) | Self::Parse(_) => 1,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct GitTreeEntry {
    path: String,
    mode: String,
    kind: String,
    blob: String,
    size: Option<u64>,
}

#[derive(Debug, Clone, Serialize)]
struct AuditRecord {
    path: String,
    rule: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    description: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    before: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    after: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    before_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    after_sha256: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct PatchManifest {
    schema_version: String,
    #[serde(default)]
    patches: Vec<PatchEntry>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct PatchEntry {
    id: String,
    status: PatchStatus,
    owner: String,
    reason: String,
    issue: String,
    reviewed_on: String,
    expires_on: String,
    #[serde(default)]
    path: Option<String>,
    #[serde(default = "default_patch_kind")]
    kind: PatchKind,
    #[serde(default)]
    rule: Option<String>,
    #[serde(default)]
    find: Option<String>,
    #[serde(default)]
    replace: Option<String>,
    #[serde(default)]
    expected_replacements: Option<usize>,
    #[serde(default)]
    allow_missing: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum PatchStatus {
    Active,
    Inactive,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum PatchKind {
    StringReplace,
    AdapterRule,
}

fn default_patch_kind() -> PatchKind {
    PatchKind::StringReplace
}

#[derive(Debug, Clone)]
struct PatchApplicationReport {
    manifest_path: PathBuf,
    schema_version: String,
    active_patch_ids: Vec<String>,
    inactive_patch_ids: Vec<String>,
    applied_patch_ids: Vec<String>,
    records: Vec<AuditRecord>,
}

impl PatchApplicationReport {
    fn empty(manifest_path: PathBuf, schema_version: String) -> Self {
        Self {
            manifest_path,
            schema_version,
            active_patch_ids: Vec::new(),
            inactive_patch_ids: Vec::new(),
            applied_patch_ids: Vec::new(),
            records: Vec::new(),
        }
    }

    fn to_json(&self, root: &Path) -> Value {
        json!({
            "path": display_path(&self.manifest_path, root),
            "schema_version": self.schema_version,
            "active_patch_count": self.active_patch_ids.len(),
            "inactive_patch_count": self.inactive_patch_ids.len(),
            "applied_patch_count": self.applied_patch_ids.len(),
            "audit_records": self.records.len(),
            "active_patch_ids": &self.active_patch_ids,
            "inactive_patch_ids": &self.inactive_patch_ids,
            "applied_patch_ids": &self.applied_patch_ids,
        })
    }
}

#[derive(Debug, Clone)]
struct RevisionResolution {
    requested_revision: String,
    requested_ref: String,
    requested_qualifier: Option<String>,
    upstream_remote: String,
    fetch_enabled: bool,
    fetch_succeeded: Option<bool>,
    source: String,
    source_detail: String,
    resolved_revision: String,
}

impl RevisionResolution {
    fn to_json(&self) -> Value {
        json!({
            "requested_revision": self.requested_revision,
            "requested_ref": self.requested_ref,
            "requested_qualifier": self.requested_qualifier,
            "upstream_remote": self.upstream_remote,
            "fetch_enabled": self.fetch_enabled,
            "fetch_succeeded": self.fetch_succeeded,
            "source": self.source,
            "source_detail": self.source_detail,
            "resolved_revision": self.resolved_revision,
        })
    }
}

/// Run the complete upstream porting workflow.
pub fn run_porting(options: PortOptions) -> Result<PortRunReport, PortError> {
    if options.execute && options.scorecard_log.is_some() {
        return Err(PortError::Message(
            "--scorecard-log is log-parse mode; pass it without --execute so scorecard evidence cannot be mistaken for a fresh suite run".to_string(),
        ));
    }
    if options.max_files.is_some() && options.apply {
        return Err(PortError::Message(
            "--max-files is a bounded smoke import and cannot be combined with apply=true; rerun without --max-files for an applying import".to_string(),
        ));
    }
    if options.max_files.is_some() && options.proof_mode == ProofMode::Full {
        return Err(PortError::Message(
            "--max-files is a bounded smoke import and cannot be combined with proof_mode=full; rerun without --max-files for full proof".to_string(),
        ));
    }

    let root = options.repo_root.canonicalize()?;
    let out_dir = root_path(&root, &options.out_dir);
    let imported = out_dir.join("imported");
    let ported = out_dir.join("ported");
    let proof_dir = out_dir.join("proof");
    let compatibility_summary_path = options
        .summary_out
        .as_deref()
        .map(|path| root_path(&root, path))
        .unwrap_or_else(|| out_dir.join("compat-summary.json"));
    let proof_mode = options.proof_mode.resolved(options.max_files);
    let test_exceptions =
        options.test_exceptions.clone().unwrap_or_else(empty_test_exception_ledger);
    let test_exception_validation_date =
        options.test_exception_validation_date.clone().unwrap_or_else(current_date_string);
    validate_test_exceptions_for_date(&test_exceptions, &test_exception_validation_date).map_err(
        |findings| {
            PortError::Message(format!(
                "test exception ledger failed validation for {test_exception_validation_date}: {}",
                findings
                    .iter()
                    .map(|finding| format!("{}: {}", finding.field, finding.message))
                    .collect::<Vec<_>>()
                    .join("; ")
            ))
        },
    )?;
    fs::create_dir_all(&out_dir)?;
    if proof_dir.exists() {
        fs::remove_dir_all(&proof_dir)?;
    }

    let resolution = resolve_revision_report(
        &root,
        &options.upstream_revision,
        &options.upstream_remote,
        options.fetch,
    )?;
    let resolved = resolution.resolved_revision.clone();
    let local_head = local_revision(&root)?;

    let entries = list_upstream_tests(&root, &resolved)?;
    let exported = export_overlay(&root, &resolved, &entries, &imported, options.max_files)?;
    let audit_jsonl = out_dir.join("adapter-audit.jsonl");
    let mut audit = adapt_overlay(&imported, &ported, &audit_jsonl)?;
    let patch_report = if let Some(manifest) = options.patch_manifest.as_deref() {
        let manifest = root_path(&root, manifest);
        let report = apply_patch_manifest(
            &root,
            &ported,
            &manifest,
            &test_exception_validation_date,
            &audit_jsonl,
        )?;
        audit.extend(report.records.clone());
        Some(report)
    } else {
        None
    };
    write_audit_markdown(&out_dir.join("adapter-audit.md"), &audit)?;

    let baseline_path = root_path(&root, &options.baseline);
    let baseline = parse_baseline_document(&baseline_path)?;
    let baseline_revision = Some(revision_ref(&baseline.upstream.revision).to_string());
    let baseline_paths = match baseline_revision.as_deref() {
        Some(revision) => list_upstream_tests(&root, revision)?
            .into_iter()
            .map(|entry| entry.path)
            .collect::<BTreeSet<_>>(),
        None => BTreeSet::new(),
    };
    let upstream_paths = entries.iter().map(|entry| entry.path.clone()).collect::<Vec<_>>();
    let upstream_path_set = upstream_paths.iter().cloned().collect::<BTreeSet<_>>();
    let stale_upstream_paths =
        baseline_paths.difference(&upstream_path_set).cloned().collect::<Vec<_>>();

    let (applied, removed_stale) = if options.apply {
        apply_ported_overlay(&root, &ported, &exported, &stale_upstream_paths)?
    } else {
        (Vec::new(), Vec::new())
    };

    let current_paths = current_test_files(&root)?;
    let missing_locally = upstream_path_set.difference(&current_paths).cloned().collect::<Vec<_>>();
    let extra_locally = current_paths.difference(&upstream_path_set).cloned().collect::<Vec<_>>();

    let mut execution_exit_status = None;
    let mut execution_log_path = None;
    let mut scorecard_log_path = None;
    let mut cargo_driver = None;
    let mut execution_telemetry = Value::Null;

    if let Some(log) = options.scorecard_log.as_deref() {
        let input_log = root_path(&root, log);
        if !input_log.exists() {
            return Err(PortError::Message(format!(
                "scorecard log does not exist: {}",
                input_log.display()
            )));
        }
        let copied_log = out_dir.join("execution.log");
        if !same_path(&input_log, &copied_log) {
            fs::copy(&input_log, &copied_log)?;
        }
        execution_log_path = Some(copied_log.clone());
        scorecard_log_path = Some(copied_log);
    } else if options.execute {
        let execution = execute_suite(
            &root,
            &out_dir,
            &resolved,
            &options.bootstrap_args,
            options.target_triple.as_deref(),
            options.host_triple.as_deref(),
            options.release,
            options.max_files,
            &entries,
            &exported,
            &local_head,
            &test_exceptions,
            &test_exception_validation_date,
        )?;
        execution_exit_status = Some(execution.exit_status);
        execution_log_path = Some(execution.execution_log);
        scorecard_log_path = Some(execution.scorecard_log);
        cargo_driver = Some(execution.cargo_driver.join(" "));
        execution_telemetry = execution.telemetry;
    }

    let mut scorecard = match scorecard_log_path.as_deref() {
        Some(path) => parse_scorecard(path, &test_exceptions, &test_exception_validation_date)?,
        None => parse_scorecard(
            &out_dir.join("missing.log"),
            &test_exceptions,
            &test_exception_validation_date,
        )?,
    };

    let upstream_fixes_path = root_path(&root, &options.upstream_fixes);
    let fix_ledger = read_upstream_fix_ledger(&upstream_fixes_path)?;
    let llm_directives_path = options
        .llm_directives
        .as_deref()
        .map(|path| root_path(&root, path))
        .unwrap_or_else(|| out_dir.join("llm-directives.md"));
    let proof_validation = proof_artifact_validation(
        &proof_dir,
        options.release,
        &test_exceptions,
        &test_exception_validation_date,
        options.max_files.is_some(),
    )?;
    let proof_artifacts_complete =
        proof_validation.get("complete").and_then(Value::as_bool).unwrap_or(false);
    let proof_required = proof_required_for_exit(options.execute, proof_mode);

    set_object_field(&mut scorecard, "upstream_revision", json!(options.upstream_revision));
    set_object_field(
        &mut scorecard,
        "requested_upstream_revision",
        json!(options.upstream_revision),
    );
    set_object_field(&mut scorecard, "requested_upstream_ref", json!(resolution.requested_ref));
    set_object_field(&mut scorecard, "upstream_remote", json!(options.upstream_remote));
    set_object_field(&mut scorecard, "upstream_resolution", resolution.to_json());
    set_object_field(&mut scorecard, "resolved_upstream_revision", json!(resolved));
    set_object_field(&mut scorecard, "local_repository_revision", json!(local_head));
    set_object_field(&mut scorecard, "baseline_revision", json!(baseline_revision));
    set_object_field(
        &mut scorecard,
        "upstream_revision_drift",
        revision_drift(
            baseline_revision.as_deref(),
            &options.upstream_revision,
            &resolved,
            &options.upstream_remote,
            &resolution.source,
        ),
    );
    set_object_field(
        &mut scorecard,
        "upstream_fix_accounting",
        upstream_fix_accounting(&fix_ledger, baseline_revision.as_deref(), &resolved),
    );
    set_object_field(&mut scorecard, "imported_files", json!(exported.len()));
    set_object_field(&mut scorecard, "upstream_test_files", json!(entries.len()));
    set_object_field(&mut scorecard, "ported_audit_records", json!(audit.len()));
    set_object_field(
        &mut scorecard,
        "patch_manifest_accounting",
        patch_report
            .as_ref()
            .map(|report| report.to_json(&root))
            .unwrap_or_else(|| json!({"path": null, "active_patch_count": 0, "applied_patch_count": 0, "audit_records": 0})),
    );
    set_object_field(
        &mut scorecard,
        "test_exception_accounting",
        test_exception_accounting(&test_exceptions, &test_exception_validation_date),
    );
    set_object_field(
        &mut scorecard,
        "llm_directives_path",
        json!(display_path(&llm_directives_path, &root)),
    );
    set_object_field(
        &mut scorecard,
        "ported_files_with_edits",
        json!(audit.iter().map(|row| row.path.as_str()).collect::<BTreeSet<_>>().len()),
    );
    set_object_field(&mut scorecard, "applied_files", json!(applied.len()));
    set_object_field(&mut scorecard, "removed_stale_upstream_files", json!(removed_stale.len()));
    set_object_field(&mut scorecard, "stale_upstream_paths", json!(stale_upstream_paths));
    set_object_field(&mut scorecard, "missing_locally", json!(missing_locally));
    set_object_field(&mut scorecard, "extra_locally", json!(extra_locally));
    set_object_field(
        &mut scorecard,
        "primary_upstream_tests",
        json!(unique_primary_paths(&upstream_paths)),
    );
    set_object_field(
        &mut scorecard,
        "primary_extra_local_tests",
        json!(unique_primary_paths(
            &current_paths.difference(&upstream_path_set).cloned().collect::<Vec<_>>()
        )),
    );
    set_object_field(&mut scorecard, "execution_exit_status", json!(execution_exit_status));
    set_object_field(&mut scorecard, "execution_telemetry", execution_telemetry);
    set_object_field(&mut scorecard, "trust_cargo_driver", json!(cargo_driver));
    set_object_field(&mut scorecard, "proof_mode", json!(proof_mode.label()));
    set_object_field(&mut scorecard, "proof_required_for_exit", json!(proof_required));
    set_object_field(
        &mut scorecard,
        "proof_accounting_status",
        json!(proof_accounting_status(
            options.execute,
            proof_mode,
            proof_artifacts_complete,
            execution_exit_status
        )),
    );
    set_object_field(&mut scorecard, "proof_artifacts_complete", json!(proof_artifacts_complete));
    set_object_field(
        &mut scorecard,
        "missing_proof_artifacts",
        proof_validation.get("missing").cloned().unwrap_or_else(|| json!([])),
    );
    set_object_field(
        &mut scorecard,
        "invalid_proof_artifacts",
        proof_validation.get("invalid").cloned().unwrap_or_else(|| json!([])),
    );
    set_object_field(&mut scorecard, "proof_artifact_validation", proof_validation);
    set_object_field(
        &mut scorecard,
        "artifacts",
        json!({
            "imported": display_path(&imported, &root),
            "ported": display_path(&ported, &root),
            "adapter_audit_jsonl": display_path(&audit_jsonl, &root),
            "adapter_audit_md": display_path(&out_dir.join("adapter-audit.md"), &root),
            "patch_manifest": patch_report.as_ref().map(|report| display_path(&report.manifest_path, &root)),
            "llm_directives": display_path(&llm_directives_path, &root),
            "scorecard_json": display_path(&out_dir.join("scorecard.json"), &root),
            "scorecard_md": display_path(&out_dir.join("scorecard.md"), &root),
            "compatibility_summary": display_path(&compatibility_summary_path, &root),
            "execution_log": execution_log_path.as_ref().map(|path| display_path(path, &root)),
            "scorecard_source_log": scorecard_log_path.as_ref().map(|path| display_path(path, &root)),
            "proof_dir": display_path(&proof_dir, &root),
            "proof_inventory": existing_artifact_path(&proof_dir.join("inventory.json"), &root),
            "proof_results": existing_artifact_path(&proof_dir.join("results.json"), &root),
            "proof_summary": existing_artifact_path(&proof_dir.join("proof-summary.json"), &root),
        }),
    );

    let validation_failures = scorecard_validation_failures(&scorecard);
    let validation_failures = append_porting_validation_failures(
        validation_failures,
        options.execute,
        options.max_files,
        &missing_locally,
    );
    set_object_field(
        &mut scorecard,
        "validation_failures",
        Value::Array(validation_failures.clone()),
    );

    write_llm_directives(
        &llm_directives_path,
        &scorecard,
        &test_exceptions,
        &test_exception_validation_date,
        patch_report.as_ref(),
        &fix_ledger,
        &root,
    )?;
    write_json(
        &out_dir.join("upstream-inventory.json"),
        &json!({
            "upstream_revision": options.upstream_revision,
            "requested_upstream_ref": resolution.requested_ref,
            "upstream_remote": options.upstream_remote,
            "upstream_resolution": resolution.to_json(),
            "resolved_upstream_revision": resolved,
            "local_repository_revision": local_head,
            "tests": entries,
        }),
    )?;
    write_json(&out_dir.join("scorecard.json"), &scorecard)?;
    write_scorecard_markdown(&out_dir.join("scorecard.md"), &scorecard)?;

    let base_exit = scorecard_exit_code(
        &scorecard,
        options.execute,
        execution_exit_status,
        &validation_failures,
    );
    let exit_code = if base_exit != 0 {
        base_exit
    } else {
        porting_exit_code(&scorecard, options.execute, proof_mode)
    };
    let compatibility_summary = compatibility_summary_from_porting(
        &root,
        &baseline,
        &scorecard,
        &options,
        &compatibility_summary_path,
        &resolved,
        &local_head,
        exit_code,
    )?;
    write_json(&compatibility_summary_path, &serde_json::to_value(compatibility_summary)?)?;

    Ok(PortRunReport {
        exit_code,
        requested_revision: options.upstream_revision,
        requested_ref: resolution.requested_ref,
        upstream_remote: options.upstream_remote,
        resolution_source: resolution.source,
        resolution_detail: resolution.source_detail,
        resolved_revision: resolved,
        local_revision: local_head,
        imported_files: exported.len(),
        upstream_test_files: entries.len(),
        audit_records: audit.len(),
        patch_records: patch_report.as_ref().map_or(0, |report| report.records.len()),
        llm_directives_path,
        scorecard_path: out_dir.join("scorecard.md"),
        compatibility_summary_path,
        failed_tests: scorecard_total(&scorecard, "failed"),
        tool_failures: scorecard_total(&scorecard, "tool_failures"),
        validation_failures,
    })
}

fn root_path(root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() { path.to_path_buf() } else { root.join(path) }
}

fn compatibility_summary_from_porting(
    root: &Path,
    baseline: &CompatibilityBaseline,
    scorecard: &Value,
    options: &PortOptions,
    compatibility_summary_path: &Path,
    resolved_upstream_revision: &str,
    local_head: &str,
    exit_code: u8,
) -> Result<CompatibilityResultSummary, PortError> {
    let all_compatible = compatibility_summary_is_admissible_pass(scorecard, options, exit_code);
    let observed = compatibility_summary_observed(scorecard, options, all_compatible);
    let results = baseline
        .entries
        .iter()
        .map(|entry| CompatibilityResult {
            baseline_entry_id: entry.id.clone(),
            outcome: if all_compatible {
                CompatibilityOutcome::Compatible
            } else {
                CompatibilityOutcome::Unknown
            },
            observed: Some(observed.clone()),
            exception_id: None,
            upstream_fix_id: None,
        })
        .collect::<Vec<_>>();
    let host_triple = current_host_triple();
    let target_arch = options.target_arch.clone().unwrap_or_else(|| env::consts::ARCH.to_string());
    let target_triple = options.target_triple.clone().or_else(|| host_triple.clone());
    let target = options
        .target
        .clone()
        .or_else(|| target_triple.clone())
        .or_else(|| Some(target_arch.clone()));
    let host_triple = options.host_triple.clone().or(host_triple);
    let host = options.host.clone().or_else(|| host_triple.clone());
    let run_id =
        options.run_id.clone().unwrap_or_else(|| format!("upstream-port-{}", current_timestamp()));
    let proof_mode = options.proof_mode.resolved(options.max_files);
    let summary_out = display_path(compatibility_summary_path, root);
    let out_dir = display_path(&root_path(root, &options.out_dir), root);
    let release_facing_argv = release_facing_upstream_tests_argv(
        options,
        proof_mode,
        &summary_out,
        &out_dir,
        &run_id,
        &target_arch,
        target.as_deref(),
        target_triple.as_deref(),
        host.as_deref(),
        host_triple.as_deref(),
    );
    let mut runner_metadata = BTreeMap::new();
    runner_metadata.insert("release".to_string(), json!(options.release));
    runner_metadata.insert("execute".to_string(), json!(options.execute));
    runner_metadata.insert("apply".to_string(), json!(options.apply));
    runner_metadata.insert("fetch".to_string(), json!(options.fetch));
    runner_metadata.insert("proof_mode".to_string(), json!(proof_mode.label()));
    runner_metadata.insert("proof_mode_requested".to_string(), json!(options.proof_mode.label()));
    runner_metadata.insert("proof_mode_resolved".to_string(), json!(proof_mode.label()));
    runner_metadata.insert("run_id".to_string(), json!(run_id.clone()));
    runner_metadata.insert("target_arch".to_string(), json!(target_arch.clone()));
    runner_metadata.insert("target".to_string(), json!(target.clone()));
    runner_metadata.insert("target_triple".to_string(), json!(target_triple.clone()));
    runner_metadata.insert("host".to_string(), json!(host.clone()));
    runner_metadata.insert("host_triple".to_string(), json!(host_triple.clone()));
    runner_metadata.insert("summary_out".to_string(), json!(summary_out.clone()));
    runner_metadata.insert("out_dir".to_string(), json!(out_dir.clone()));
    runner_metadata.insert("argv".to_string(), json!(release_facing_argv.clone()));
    runner_metadata.insert("argv_kind".to_string(), json!("release_facing_canonical"));
    runner_metadata
        .insert("release_facing_command".to_string(), json!(shell_join(&release_facing_argv)));
    runner_metadata.insert(
        "release_evidence_contract".to_string(),
        json!({
            "entrypoint": "targo trust domination upstream-tests",
            "release": options.release,
            "execute": options.execute,
            "proof_mode": proof_mode.label(),
            "summary_out": summary_out,
            "out_dir": out_dir,
            "run_id": run_id.clone(),
            "target_arch": target_arch.clone(),
            "target": target.clone(),
            "target_triple": target_triple.clone(),
            "host": host.clone(),
            "host_triple": host_triple.clone(),
            "requires_release": true,
            "requires_execute": true,
            "requires_proof_mode": "full",
            "requires_summary_out": true,
            "satisfied": options.release
                && options.execute
                && options.max_files.is_none()
                && proof_mode == ProofMode::Full
                && options.summary_out.is_some(),
        }),
    );

    Ok(CompatibilityResultSummary {
        schema_version: crate::SCHEMA_VERSION.to_string(),
        baseline_id: baseline.id.clone(),
        generated_on: current_date_string(),
        run_id: Some(run_id),
        repo_head: Some(local_head.to_string()),
        repo_dirty: Some(repo_dirty(root)?),
        upstream_revision: Some(format!(
            "{}:{}",
            options.upstream_remote, resolved_upstream_revision
        )),
        target_arch: Some(target_arch.clone()),
        target,
        target_triple,
        host,
        host_triple,
        architecture: Some(target_arch),
        runner: Some(CompatibilitySummaryRunner {
            python_used: Some(false),
            implementation: Some(json!("rust")),
            entrypoint: Some(json!("targo trust domination upstream-tests")),
            command: Some(json!("trust-upstream-compat port")),
            tool: Some(json!("trust-upstream-compat")),
            metadata: runner_metadata,
            ..CompatibilitySummaryRunner::default()
        }),
        totals: ResultTotals::from_results(&results),
        results,
    })
}

#[allow(clippy::too_many_arguments)]
fn release_facing_upstream_tests_argv(
    options: &PortOptions,
    proof_mode: ProofMode,
    summary_out: &str,
    out_dir: &str,
    run_id: &str,
    target_arch: &str,
    target: Option<&str>,
    target_triple: Option<&str>,
    host: Option<&str>,
    host_triple: Option<&str>,
) -> Vec<String> {
    let mut argv = vec![
        "targo".to_string(),
        "trust".to_string(),
        "domination".to_string(),
        "upstream-tests".to_string(),
    ];
    if options.release {
        argv.push("--release".to_string());
    }
    argv.extend(["--proof-mode".to_string(), proof_mode.label().to_string()]);
    argv.push(if options.execute { "--execute" } else { "--no-execute" }.to_string());
    argv.push(if options.apply { "--apply" } else { "--no-apply" }.to_string());
    if !options.fetch {
        argv.push("--no-fetch".to_string());
    }
    argv.extend(["--summary-out".to_string(), summary_out.to_string()]);
    argv.extend(["--out-dir".to_string(), out_dir.to_string()]);
    argv.extend(["--run-id".to_string(), run_id.to_string()]);
    argv.extend(["--target-arch".to_string(), target_arch.to_string()]);
    if let Some(target) = target {
        argv.extend(["--target".to_string(), target.to_string()]);
    }
    if let Some(target_triple) = target_triple {
        argv.extend(["--target-triple".to_string(), target_triple.to_string()]);
    }
    if let Some(host) = host {
        argv.extend(["--host".to_string(), host.to_string()]);
    }
    if let Some(host_triple) = host_triple {
        argv.extend(["--host-triple".to_string(), host_triple.to_string()]);
    }
    argv.extend(["--upstream-revision".to_string(), options.upstream_revision.clone()]);
    argv.extend(["--upstream-remote".to_string(), options.upstream_remote.clone()]);
    if let Some(max_files) = options.max_files {
        argv.extend(["--max-files".to_string(), max_files.to_string()]);
    }
    argv
}

fn compatibility_summary_observed(
    scorecard: &Value,
    options: &PortOptions,
    all_compatible: bool,
) -> String {
    format!(
        "upstream porting scorecard {}; failed_tests={} tool_failures={} validation_failures={} proof_artifacts_complete={} execute={} release={}",
        if all_compatible { "passed" } else { "not release-clean" },
        scorecard_total(scorecard, "failed"),
        scorecard_total(scorecard, "tool_failures"),
        scorecard.get("validation_failures").and_then(Value::as_array).map_or(0, Vec::len),
        scorecard.get("proof_artifacts_complete").and_then(Value::as_bool).unwrap_or(false),
        options.execute,
        options.release,
    )
}

fn compatibility_summary_is_admissible_pass(
    scorecard: &Value,
    options: &PortOptions,
    exit_code: u8,
) -> bool {
    exit_code == 0
        && options.release
        && options.execute
        && options.max_files.is_none()
        && options.proof_mode.resolved(options.max_files) == ProofMode::Full
        && scorecard_total(scorecard, "failed") == 0
        && scorecard_total(scorecard, "tool_failures") == 0
        && scorecard.get("validation_failures").and_then(Value::as_array).is_some_and(Vec::is_empty)
        && scorecard.get("proof_artifacts_complete").and_then(Value::as_bool).unwrap_or(false)
}

fn repo_dirty(root: &Path) -> Result<bool, PortError> {
    let output = git(
        root,
        &["status", "--porcelain=v1", "--untracked-files=all", "--ignore-submodules=none"],
    )?;
    Ok(!output.trim().is_empty())
}

fn current_host_triple() -> Option<String> {
    let output = Command::new("rustc").arg("-vV").output().ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .find_map(|line| line.strip_prefix("host: ").map(str::to_string))
}

fn existing_artifact_path(path: &Path, root: &Path) -> Option<String> {
    path.exists().then(|| display_path(path, root))
}

fn same_path(left: &Path, right: &Path) -> bool {
    match (left.canonicalize(), right.canonicalize()) {
        (Ok(left), Ok(right)) => left == right,
        _ => left == right,
    }
}

fn set_object_field(object: &mut Value, key: &str, value: Value) {
    if !object.is_object() {
        *object = json!({});
    }
    object.as_object_mut().expect("object initialized").insert(key.to_string(), value);
}

fn run_capture(
    root: &Path,
    program: &str,
    args: &[&str],
    check: bool,
) -> Result<Vec<u8>, PortError> {
    let output = Command::new(program).args(args).current_dir(root).output()?;
    if check && !output.status.success() {
        return Err(PortError::CommandFailed {
            command: shell_join(
                std::iter::once(program.to_string())
                    .chain(args.iter().map(|arg| (*arg).to_string()))
                    .collect::<Vec<_>>()
                    .as_slice(),
            ),
            status: output.status,
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        });
    }
    Ok(output.stdout)
}

fn git(root: &Path, args: &[&str]) -> Result<String, PortError> {
    let stdout = run_capture(root, "git", args, true)?;
    Ok(String::from_utf8_lossy(&stdout).into_owned())
}

fn git_maybe(root: &Path, args: &[&str]) -> Result<(ExitStatus, String, String), PortError> {
    let output = Command::new("git").args(args).current_dir(root).output()?;
    Ok((
        output.status,
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    ))
}

fn revision_ref(spec: &str) -> &str {
    spec.split_once(':').map_or(spec, |(_, ref_name)| ref_name)
}

fn revision_qualifier(spec: &str) -> Option<&str> {
    spec.split_once(':').map(|(qualifier, _)| qualifier)
}

fn is_remote_qualified_revision(spec: &str) -> bool {
    spec.contains(':')
}

fn is_full_commit_hash(value: &str) -> bool {
    let value = value.trim();
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn resolve_revision_report(
    root: &Path,
    spec: &str,
    remote: &str,
    fetch: bool,
) -> Result<RevisionResolution, PortError> {
    let ref_name = revision_ref(spec);
    let qualified = is_remote_qualified_revision(spec);
    if fetch {
        let (status, _stdout, stderr) = git_maybe(root, &["fetch", "--no-tags", remote, ref_name])?;
        if status.success() {
            let resolved =
                git(root, &["rev-parse", "--verify", "FETCH_HEAD^{commit}"])?.trim().to_string();
            return Ok(RevisionResolution {
                requested_revision: spec.to_string(),
                requested_ref: ref_name.to_string(),
                requested_qualifier: revision_qualifier(spec).map(str::to_string),
                upstream_remote: remote.to_string(),
                fetch_enabled: true,
                fetch_succeeded: Some(true),
                source: "remote-fetch".to_string(),
                source_detail: format!("fetched ref '{ref_name}' from {remote}"),
                resolved_revision: resolved,
            });
        }

        let (_local_status, local, _local_stderr) =
            git_maybe(root, &["rev-parse", "--verify", &format!("{ref_name}^{{commit}}")])?;
        let local = local.trim();
        if !local.is_empty() && (!qualified || is_full_commit_hash(ref_name)) {
            return Ok(RevisionResolution {
                requested_revision: spec.to_string(),
                requested_ref: ref_name.to_string(),
                requested_qualifier: revision_qualifier(spec).map(str::to_string),
                upstream_remote: remote.to_string(),
                fetch_enabled: true,
                fetch_succeeded: Some(false),
                source: "local-fallback-after-fetch-failure".to_string(),
                source_detail: format!(
                    "resolved local commit '{ref_name}' after fetch from {remote} failed"
                ),
                resolved_revision: local.to_string(),
            });
        }

        return Err(PortError::Message(format!(
            "failed to fetch upstream revision '{spec}' from '{remote}'\nref '{ref_name}' is remote-qualified and was not resolved against local repository refs\n{stderr}"
        )));
    }

    if qualified && !is_full_commit_hash(ref_name) {
        return Err(PortError::Message(format!(
            "cannot resolve remote-qualified upstream revision '{spec}' with fetch disabled\nref '{ref_name}' is symbolic; enable fetch or pass an exact upstream commit"
        )));
    }

    let resolved = git(root, &["rev-parse", "--verify", &format!("{ref_name}^{{commit}}")])?
        .trim()
        .to_string();
    Ok(RevisionResolution {
        requested_revision: spec.to_string(),
        requested_ref: ref_name.to_string(),
        requested_qualifier: revision_qualifier(spec).map(str::to_string),
        upstream_remote: remote.to_string(),
        fetch_enabled: false,
        fetch_succeeded: None,
        source: "local-ref-no-fetch".to_string(),
        source_detail: format!("resolved local ref '{ref_name}' with fetch disabled"),
        resolved_revision: resolved,
    })
}

fn local_revision(root: &Path) -> Result<String, PortError> {
    Ok(git(root, &["rev-parse", "--verify", "HEAD^{commit}"])?.trim().to_string())
}

fn parse_ls_tree(output: &str) -> Result<Vec<GitTreeEntry>, PortError> {
    let mut entries = Vec::new();
    for line in output.lines() {
        let Some((metadata, path)) = line.split_once('\t') else {
            continue;
        };
        if !path.starts_with(UPSTREAM_TEST_PREFIX) {
            continue;
        }
        let mut parts = metadata.split_whitespace();
        let Some(mode) = parts.next() else { continue };
        let Some(kind) = parts.next() else { continue };
        let Some(blob) = parts.next() else { continue };
        let Some(size) = parts.next() else { continue };
        entries.push(GitTreeEntry {
            path: path.to_string(),
            mode: mode.to_string(),
            kind: kind.to_string(),
            blob: blob.to_string(),
            size: if size == "-" {
                None
            } else {
                Some(size.parse::<u64>().map_err(|_| {
                    PortError::Message(format!("invalid git ls-tree size '{size}' for {path}"))
                })?)
            },
        });
    }
    Ok(entries)
}

fn list_upstream_tests(root: &Path, revision: &str) -> Result<Vec<GitTreeEntry>, PortError> {
    parse_ls_tree(&git(root, &["ls-tree", "-r", "-l", revision, "--", "tests"])?)
}

fn export_overlay(
    root: &Path,
    revision: &str,
    entries: &[GitTreeEntry],
    destination: &Path,
    max_files: Option<usize>,
) -> Result<Vec<String>, PortError> {
    if destination.exists() {
        fs::remove_dir_all(destination)?;
    }
    fs::create_dir_all(destination)?;

    if max_files.is_none() {
        let mut archive = Command::new("git")
            .args(["archive", "--format=tar", revision, "tests"])
            .current_dir(root)
            .stdout(Stdio::piped())
            .spawn()?;
        let archive_stdout = archive.stdout.take().ok_or_else(|| {
            PortError::Message("failed to capture git archive stdout".to_string())
        })?;
        let extract = Command::new("tar")
            .args(["-xf", "-", "-C"])
            .arg(destination)
            .stdin(Stdio::from(archive_stdout))
            .output()?;
        let archive_status = archive.wait()?;
        if !archive_status.success() || !extract.status.success() {
            return Err(PortError::Message(format!(
                "failed to export upstream tests with git archive\ngit archive status: {archive_status}\ntar status: {}\ntar stdout:\n{}\ntar stderr:\n{}",
                extract.status,
                String::from_utf8_lossy(&extract.stdout),
                String::from_utf8_lossy(&extract.stderr)
            )));
        }
        return Ok(entries.iter().map(|entry| entry.path.clone()).collect());
    }

    let mut exported = Vec::new();
    for entry in entries {
        if max_files.is_some_and(|limit| exported.len() >= limit) {
            break;
        }
        let output = Command::new("git")
            .arg("show")
            .arg(format!("{revision}:{}", entry.path))
            .current_dir(root)
            .output()?;
        if !output.status.success() {
            continue;
        }
        let target = destination.join(&entry.path);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&target, output.stdout)?;
        exported.push(entry.path.clone());
    }
    Ok(exported)
}

fn copy_dir_all(source: &Path, destination: &Path) -> Result<(), PortError> {
    fs::create_dir_all(destination)?;
    for entry in fs::read_dir(source)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        let target = destination.join(entry.file_name());
        if file_type.is_dir() {
            copy_dir_all(&entry.path(), &target)?;
        } else if file_type.is_file() {
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::copy(entry.path(), target)?;
        }
    }
    Ok(())
}

fn adapt_overlay(
    imported: &Path,
    ported: &Path,
    audit_jsonl: &Path,
) -> Result<Vec<AuditRecord>, PortError> {
    if ported.exists() {
        fs::remove_dir_all(ported)?;
    }
    copy_dir_all(imported, ported)?;
    if let Some(parent) = audit_jsonl.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut audit_writer = BufWriter::new(File::create(audit_jsonl)?);
    audit_writer.flush()?;
    Ok(Vec::new())
}

fn apply_patch_manifest(
    root: &Path,
    ported: &Path,
    manifest_path: &Path,
    validation_date: &str,
    audit_jsonl: &Path,
) -> Result<PatchApplicationReport, PortError> {
    if !manifest_path.is_file() {
        return Err(PortError::Message(format!(
            "upstream patch manifest is required but missing: {}",
            display_path(manifest_path, root)
        )));
    }

    let manifest_text = fs::read_to_string(manifest_path)?;
    let manifest: PatchManifest = toml::from_str(&manifest_text).map_err(|err| {
        PortError::Message(format!(
            "failed to parse upstream patch manifest {}: {err}",
            display_path(manifest_path, root)
        ))
    })?;
    validate_patch_manifest(&manifest, manifest_path, validation_date, root)?;

    let mut report =
        PatchApplicationReport::empty(manifest_path.to_path_buf(), manifest.schema_version.clone());
    let mut audit_writer =
        BufWriter::new(OpenOptions::new().create(true).append(true).open(audit_jsonl)?);

    for patch in &manifest.patches {
        match patch.status {
            PatchStatus::Inactive => {
                report.inactive_patch_ids.push(patch.id.clone());
                continue;
            }
            PatchStatus::Active => report.active_patch_ids.push(patch.id.clone()),
        }

        match patch.kind {
            PatchKind::StringReplace => {
                apply_string_replace_patch(ported, patch, &mut report, &mut audit_writer)?
            }
            PatchKind::AdapterRule => {
                apply_adapter_rule_patch(ported, patch, &mut report, &mut audit_writer)?
            }
        }
    }

    audit_writer.flush()?;
    Ok(report)
}

fn apply_string_replace_patch(
    ported: &Path,
    patch: &PatchEntry,
    report: &mut PatchApplicationReport,
    audit_writer: &mut dyn Write,
) -> Result<(), PortError> {
    let rel = normalize_patch_entry_path(required_patch_path(patch)?)?;
    let target = ported.join(Path::new(&rel));
    if !target.is_file() {
        if patch.allow_missing {
            return Ok(());
        }
        return Err(PortError::Message(format!(
            "active upstream patch '{}' target is missing from imported overlay: {}",
            patch.id, rel
        )));
    }

    let find = required_patch_find(patch)?;
    let replace = required_patch_replace(patch)?;
    let before = fs::read_to_string(&target).map_err(|err| {
        PortError::Message(format!(
            "active upstream patch '{}' target is not readable UTF-8 text ({}): {err}",
            patch.id, rel
        ))
    })?;
    let positions = before.match_indices(find).map(|(offset, _)| offset).collect::<Vec<_>>();
    if positions.is_empty() {
        if patch.allow_missing {
            return Ok(());
        }
        return Err(PortError::Message(format!(
            "active upstream patch '{}' did not match imported overlay file {}",
            patch.id, rel
        )));
    }
    if let Some(expected) = patch.expected_replacements
        && positions.len() != expected
    {
        return Err(PortError::Message(format!(
            "active upstream patch '{}' matched {} replacements in {}, expected {}",
            patch.id,
            positions.len(),
            rel,
            expected
        )));
    }

    let before_digest = sha256_bytes(before.as_bytes());
    let after = before.replace(find, replace);
    fs::write(&target, after.as_bytes())?;
    report.applied_patch_ids.push(patch.id.clone());

    for position in positions {
        let record = AuditRecord {
            path: rel.clone(),
            rule: format!("patch_manifest:{}", patch.id),
            line: Some(line_number_at_byte_offset(&before, position)),
            description: Some(format!("{}; owner={}", patch.reason, patch.owner)),
            before: Some(find.to_string()),
            after: Some(replace.to_string()),
            before_sha256: None,
            after_sha256: None,
        };
        write_jsonl(audit_writer, &record)?;
        report.records.push(record);
    }

    let digest_record = AuditRecord {
        path: rel,
        rule: format!("patch_manifest:{}:file_digest", patch.id),
        line: None,
        description: Some("Digest after deterministic manifest patch application.".to_string()),
        before: None,
        after: None,
        before_sha256: Some(before_digest),
        after_sha256: Some(sha256_bytes(after.as_bytes())),
    };
    write_jsonl(audit_writer, &digest_record)?;
    report.records.push(digest_record);
    Ok(())
}

fn apply_adapter_rule_patch(
    ported: &Path,
    patch: &PatchEntry,
    report: &mut PatchApplicationReport,
    audit_writer: &mut dyn Write,
) -> Result<(), PortError> {
    let rule = required_patch_rule(patch)?;
    let mut files = Vec::new();
    collect_files(ported, &mut files)?;
    files.sort();
    let patch_records_before = report.records.len();
    let mut changed_files = BTreeSet::<String>::new();

    for path in files {
        let rel = path
            .strip_prefix(ported)
            .map_err(|_| {
                PortError::Message(format!("ported path escaped root: {}", path.display()))
            })?
            .to_string_lossy()
            .replace('\\', "/");
        if !is_text_path(&rel) {
            continue;
        }
        let raw = fs::read(&path)?;
        let Ok(text) = String::from_utf8(raw.clone()) else {
            continue;
        };
        let before_digest = sha256_bytes(&raw);
        let mut changed = false;
        let mut updated = String::new();
        for (index, line_with_newline) in text.split_inclusive('\n').enumerate() {
            let original_line_number = index + 1;
            let current = line_with_newline.to_string();
            if let Some(next) = apply_adapter_rule(rule, &rel, &current)
                && next != current
            {
                let record = AuditRecord {
                    path: rel.clone(),
                    rule: format!("patch_manifest:{}:{rule}", patch.id),
                    line: Some(original_line_number),
                    description: Some(format!(
                        "{}; {}; owner={}",
                        patch.reason,
                        adapter_rule_description(rule),
                        patch.owner
                    )),
                    before: Some(current.trim_end_matches('\n').to_string()),
                    after: Some(next.trim_end_matches('\n').to_string()),
                    before_sha256: None,
                    after_sha256: None,
                };
                write_jsonl(audit_writer, &record)?;
                report.records.push(record);
                updated.push_str(&next);
                changed = true;
                continue;
            }
            updated.push_str(&current);
        }
        if changed {
            fs::write(&path, updated.as_bytes())?;
            changed_files.insert(rel.clone());
            let digest_record = AuditRecord {
                path: rel,
                rule: format!("patch_manifest:{}:{rule}:file_digest", patch.id),
                line: None,
                description: Some(
                    "Digest after deterministic manifest adapter-rule application.".to_string(),
                ),
                before: None,
                after: None,
                before_sha256: Some(before_digest),
                after_sha256: Some(sha256_bytes(updated.as_bytes())),
            };
            write_jsonl(audit_writer, &digest_record)?;
            report.records.push(digest_record);
        }
    }

    let replacements = report.records.len().saturating_sub(patch_records_before);
    if replacements == 0 {
        if patch.allow_missing {
            return Ok(());
        }
        return Err(PortError::Message(format!(
            "active upstream adapter-rule patch '{}' did not modify the imported overlay",
            patch.id
        )));
    }
    if let Some(expected) = patch.expected_replacements
        && replacements != expected
    {
        return Err(PortError::Message(format!(
            "active upstream adapter-rule patch '{}' wrote {} audit records, expected {}",
            patch.id, replacements, expected
        )));
    }
    report.applied_patch_ids.push(patch.id.clone());
    if changed_files.is_empty() && !patch.allow_missing {
        return Err(PortError::Message(format!(
            "active upstream adapter-rule patch '{}' produced audit records but no changed files",
            patch.id
        )));
    }
    Ok(())
}

fn validate_patch_manifest(
    manifest: &PatchManifest,
    manifest_path: &Path,
    validation_date: &str,
    root: &Path,
) -> Result<(), PortError> {
    if manifest.schema_version != PATCH_MANIFEST_SCHEMA_VERSION {
        return Err(PortError::Message(format!(
            "upstream patch manifest {} has schema_version '{}', expected '{}'",
            display_path(manifest_path, root),
            manifest.schema_version,
            PATCH_MANIFEST_SCHEMA_VERSION
        )));
    }

    let mut ids = BTreeSet::new();
    for patch in &manifest.patches {
        if patch.id.trim().is_empty() {
            return Err(PortError::Message(format!(
                "upstream patch manifest {} contains a patch with an empty id",
                display_path(manifest_path, root)
            )));
        }
        if !ids.insert(patch.id.as_str()) {
            return Err(PortError::Message(format!(
                "upstream patch manifest {} contains duplicate patch id '{}'",
                display_path(manifest_path, root),
                patch.id
            )));
        }
        for (field, value) in [
            ("owner", patch.owner.as_str()),
            ("reason", patch.reason.as_str()),
            ("issue", patch.issue.as_str()),
            ("reviewed_on", patch.reviewed_on.as_str()),
            ("expires_on", patch.expires_on.as_str()),
        ] {
            if value.trim().is_empty() {
                return Err(PortError::Message(format!(
                    "upstream patch '{}' in {} has empty {}",
                    patch.id,
                    display_path(manifest_path, root),
                    field
                )));
            }
        }
        if !is_yyyy_mm_dd(&patch.reviewed_on) || !is_yyyy_mm_dd(&patch.expires_on) {
            return Err(PortError::Message(format!(
                "upstream patch '{}' dates must use YYYY-MM-DD in {}",
                patch.id,
                display_path(manifest_path, root)
            )));
        }
        if patch.status == PatchStatus::Active && patch.expires_on.as_str() < validation_date {
            return Err(PortError::Message(format!(
                "active upstream patch '{}' expired on {} before validation date {}",
                patch.id, patch.expires_on, validation_date
            )));
        }
        match patch.kind {
            PatchKind::StringReplace => {
                let path = required_patch_path(patch)?;
                if required_patch_find(patch)?.is_empty() {
                    return Err(PortError::Message(format!(
                        "active upstream patch '{}' must have a non-empty find string",
                        patch.id
                    )));
                }
                let _ = required_patch_replace(patch)?;
                normalize_patch_entry_path(path)?;
            }
            PatchKind::AdapterRule => {
                let rule = required_patch_rule(patch)?;
                if !adapter_rule_ids().contains(&rule) {
                    return Err(PortError::Message(format!(
                        "active upstream patch '{}' names unknown adapter rule '{}'",
                        patch.id, rule
                    )));
                }
            }
        }
    }

    Ok(())
}

fn required_patch_path(patch: &PatchEntry) -> Result<&str, PortError> {
    patch.path.as_deref().ok_or_else(|| {
        PortError::Message(format!("active upstream patch '{}' must declare path", patch.id))
    })
}

fn required_patch_rule(patch: &PatchEntry) -> Result<&str, PortError> {
    patch.rule.as_deref().ok_or_else(|| {
        PortError::Message(format!("active upstream patch '{}' must declare rule", patch.id))
    })
}

fn required_patch_find(patch: &PatchEntry) -> Result<&str, PortError> {
    patch.find.as_deref().ok_or_else(|| {
        PortError::Message(format!("active upstream patch '{}' must declare find", patch.id))
    })
}

fn required_patch_replace(patch: &PatchEntry) -> Result<&str, PortError> {
    patch.replace.as_deref().ok_or_else(|| {
        PortError::Message(format!("active upstream patch '{}' must declare replace", patch.id))
    })
}

fn normalize_patch_entry_path(path: &str) -> Result<String, PortError> {
    let normalized = path.replace('\\', "/");
    let relative = Path::new(&normalized);
    if relative.is_absolute()
        || relative.components().any(|component| {
            matches!(component, std::path::Component::ParentDir | std::path::Component::Prefix(_))
        })
    {
        return Err(PortError::Message(format!(
            "upstream patch path must be a repository-relative tests/ path: {path}"
        )));
    }
    if !normalized.starts_with("tests/") || !is_text_path(&normalized) {
        return Err(PortError::Message(format!(
            "upstream patch path must target a text file under tests/: {path}"
        )));
    }
    Ok(normalized)
}

fn line_number_at_byte_offset(text: &str, offset: usize) -> usize {
    text[..offset].bytes().filter(|byte| *byte == b'\n').count() + 1
}

fn is_yyyy_mm_dd(value: &str) -> bool {
    let bytes = value.as_bytes();
    bytes.len() == 10
        && bytes[4] == b'-'
        && bytes[7] == b'-'
        && bytes.iter().enumerate().all(|(idx, byte)| matches!(idx, 4 | 7) || byte.is_ascii_digit())
}

fn collect_files(dir: &Path, files: &mut Vec<PathBuf>) -> Result<(), PortError> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            collect_files(&path, files)?;
        } else {
            files.push(path);
        }
    }
    Ok(())
}

fn write_jsonl<T: Serialize>(writer: &mut dyn Write, value: &T) -> Result<(), PortError> {
    serde_json::to_writer(&mut *writer, value)?;
    writer.write_all(b"\n")?;
    Ok(())
}

fn is_text_path(path: &str) -> bool {
    TEXT_SUFFIXES.iter().any(|suffix| path.ends_with(suffix))
}

fn adapter_rule_ids() -> [&'static str; 14] {
    [
        "ice_issue_url",
        "ice_tool_name",
        "ice_toolchain_snapshot_note",
        "explain_tool_name",
        "calling_conventions_print_tool_name",
        "asm_labels_docs_note",
        "trust_docs_reference_notes",
        "trustc_version_normalizer",
        "print_request_docs_help",
        "refutability_docs_note",
        "terminal_error_code_url",
        "rustdoc_title_brand",
        "rustdoc_gui_title_brand",
        "rustdoc_description_brand",
    ]
}

fn adapter_rule_description(rule: &str) -> &'static str {
    match rule {
        "ice_issue_url" => "Use the Trust issue URL for ICE note expectations.",
        "ice_tool_name" => "Use the Trust driver name only in ICE note expectations.",
        "ice_toolchain_snapshot_note" => {
            "Use the Trust toolchain snapshot wording in ICE note expectations."
        }
        "explain_tool_name" => "Use the Trust compiler name in --explain help expectations.",
        "calling_conventions_print_tool_name" => {
            "Use the Trust compiler name in calling-convention print-help expectations."
        }
        "asm_labels_docs_note" => {
            "Use Trust-owned documentation wording for inline assembly label diagnostics."
        }
        "trust_docs_reference_notes" => {
            "Use Trust-owned documentation wording for diagnostic reference notes."
        }
        "trustc_version_normalizer" => {
            "Keep upstream ICE version normalizers effective after the driver rename."
        }
        "print_request_docs_help" => {
            "Use the Trust compiler documentation wording for --print help diagnostics."
        }
        "refutability_docs_note" => {
            "Use the Trust refutability documentation note in pattern-usefulness annotations."
        }
        "terminal_error_code_url" => {
            "Use Trust source links for terminal URL SVG error-code anchors."
        }
        "rustdoc_title_brand" => "Use the Trust documentation brand in rustdoc title checks.",
        "rustdoc_gui_title_brand" => {
            "Use the Trust documentation brand in rustdoc GUI title checks."
        }
        "rustdoc_description_brand" => {
            "Use the Trust documentation brand in rustdoc meta description checks."
        }
        _ => "Unknown adapter rule.",
    }
}

fn apply_adapter_rule(rule: &str, path: &str, line: &str) -> Option<String> {
    match rule {
        "ice_issue_url" if path.starts_with("tests/") && path.ends_with(".stderr") => {
            let trust_url = "https://github.com/alabsystems/Trust/issues/new?labels=C-bug%2C+I-ICE%2C+T-trustc";
            let mut next = line.replace(
                "https://github.com/rust-lang/rust/issues/new?labels=C-bug%2C+I-ICE%2C+T-compiler&template=ice.md",
                trust_url,
            );
            next = next.replace(
                "https://github.com/rust-lang/rust/issues/new?labels=C-bug%2C+I-ICE%2C+T-compiler",
                trust_url,
            );
            Some(next)
        }
        // Only genuine ICE notes name the driver: the panic banner and the
        // `note: rustc <version> running on <target>` line. A bare
        // `note: rustc…` guard also matched ordinary diagnostics whose text
        // merely starts with an identifier like `rustc_allow_const_fn_unstable`
        // and corrupted them at import.
        "ice_tool_name"
            if path_matches_python_fnmatch_star(path, "tests/ui/", ".stderr")
                && (line.contains("compiler unexpectedly panicked")
                    || (line.contains("note: rustc") && line.contains("running on"))) =>
        {
            Some(line.replace("rustc", "trustc"))
        }
        "ice_toolchain_snapshot_note"
            if path.starts_with("tests/")
                && path.ends_with(".stderr")
                && line.contains("please make sure that you have updated to the latest nightly") =>
        {
            Some(line.replace("latest nightly", "latest Trust toolchain snapshot"))
        }
        // Trust: tests that run under `-Z ui-testing=no` correctly emit the
        // invocation-derived drop-in alias (`rustc` via the rustc symlink), NOT
        // the canonical `trustc` (rustc_session::config canonicalizes
        // explain_binary to `trustc` only under ui-testing). Do NOT rebrand their
        // `--explain` expectations — they must stay `rustc --explain` to match
        // real output. Keep this list in sync with the `-Z ui-testing=no` tests.
        "explain_tool_name"
            if path.starts_with("tests/")
                && is_expected_text_path(path, line)
                && !is_ui_testing_optout_expectation(path) =>
        {
            Some(line.replace("`rustc --explain", "`trustc --explain"))
        }
        "calling_conventions_print_tool_name"
            if path.starts_with("tests/") && is_expected_text_path(path, line) =>
        {
            Some(line.replace(
                "`rustc --print=calling-conventions`",
                "`trustc --print=calling-conventions`",
            ))
        }
        "asm_labels_docs_note" if path.starts_with("tests/") && is_expected_text_path(path, line) => {
            Some(line.replace(
                "see the asm section of Rust By Example <https://doc.rust-lang.org/nightly/rust-by-example/unsafe/asm.html#labels> for more information",
                "see the Trust By Example inline assembly labels section for more information",
            ))
        }
        "trust_docs_reference_notes"
            if path.starts_with("tests/") && is_expected_text_path(path, line) =>
        {
            Some(replace_trust_docs_reference_notes(line))
        }
        "trustc_version_normalizer"
            if path_matches_python_fnmatch_star(path, "tests/ui/", ".rs")
                && line.contains("normalize-stderr")
                && line.contains("note: rustc")
                && line.contains("running on") =>
        {
            Some(line.replace("note: rustc", "note: trustc"))
        }
        "print_request_docs_help" if path.starts_with("tests/") && is_print_docs_help(line) => {
            Some(line.replace(
                "for more information, see the rustc book: https://doc.rust-lang.org/rustc/command-line-arguments.html#--print-print-compiler-information",
                "for more information, see the Trust compiler documentation for `trustc --print`",
            ))
        }
        "refutability_docs_note"
            if path_matches_python_fnmatch_star(path, "tests/ui/pattern/usefulness/", ".rs")
                && line.contains("for more information, visit") =>
        {
            Some(replace_refutability_note(line))
        }
        "terminal_error_code_url"
            if path.starts_with("tests/ui/diagnostic-flags/terminal_urls")
                && path.ends_with(".svg") =>
        {
            Some(replace_error_code_urls(line))
        }
        "rustdoc_title_brand"
            if path_matches_python_fnmatch_star(path, "tests/rustdoc-html/", ".rs")
                && line.contains("//@ has ")
                && line.contains("//head/title") =>
        {
            Some(line.replace(" - Rust'", " - Trust'"))
        }
        "rustdoc_gui_title_brand"
            if path_matches_python_fnmatch_star(path, "tests/rustdoc-gui/", ".goml")
                && (line.contains("\"title\"") || line.contains("(title,")) =>
        {
            Some(line.replace(" - Rust\"", " - Trust\""))
        }
        "rustdoc_description_brand"
            if path_matches_python_fnmatch_star(path, "tests/rustdoc-html/", ".rs")
                && line.contains("API documentation for the Rust `") =>
        {
            Some(line.replace("API documentation for the Rust", "API documentation for the Trust"))
        }
        _ => None,
    }
}

fn is_expected_text_path(path: &str, line: &str) -> bool {
    path.ends_with(".stderr")
        || path.ends_with(".stdout")
        || path.ends_with(".svg")
        || ((path.ends_with(".rs") || path.ends_with(".md")) && is_inline_expectation(line))
}

/// Trust: the ui tests compiled under `-Z ui-testing=no`, whose `--explain`
/// diagnostic correctly carries the invocation-derived drop-in name (`rustc`)
/// rather than the canonical `trustc` the porter otherwise rebrands to. Their
/// expectations must NOT be rebranded. Keep in sync with the `-Z ui-testing=no`
/// corpus (grep `ui-testing=no` under tests/ui).
fn is_ui_testing_optout_expectation(path: &str) -> bool {
    const UI_TESTING_OPTOUT_STEMS: &[&str] = &[
        "compiletest-self-test/ui-testing-optout",
        "span/issue-71363",
        "error-emitter/trimmed_multiline_suggestion",
        "modules/issue-107649",
        "consts/missing_span_in_backtrace",
    ];
    UI_TESTING_OPTOUT_STEMS.iter().any(|stem| path.contains(stem))
}

fn is_inline_expectation(line: &str) -> bool {
    line.contains("//~")
        || line.contains("//@")
        || line.contains("```compile_fail")
        || line.contains("```rust")
        || line.contains("```")
}

fn path_matches_python_fnmatch_star(path: &str, prefix: &str, suffix: &str) -> bool {
    // Python fnmatch does not make `/` special, so globs such as
    // `tests/ui/*.stderr` also match nested paths under `tests/ui/`.
    path.starts_with(prefix) && path.ends_with(suffix)
}

fn is_print_docs_help(line: &str) -> bool {
    line.contains("rustc book:")
        && line.contains("command-line-arguments.html#--print-print-compiler-information")
}

fn replace_refutability_note(line: &str) -> String {
    let needle = "for more information, visit";
    let Some(start) = line.find(needle) else {
        return line.to_string();
    };
    let rust_url = " https://doc.rust-lang.org/book/ch19-02-refutability.html";
    let end = line[start..]
        .find(rust_url)
        .map(|offset| start + offset + rust_url.len())
        .unwrap_or(start + needle.len());
    format!(
        "{}{}{}",
        &line[..start],
        "for more information, see the Trust Book's refutability section",
        &line[end..]
    )
}

fn replace_trust_docs_reference_notes(line: &str) -> String {
    let mut next = line.to_string();
    for (from, to) in [
        (
            "for more information, visit <https://doc.rust-lang.org/reference/items/traits.html#dyn-compatibility>",
            "for more information, see the Trust Reference's dyn compatibility section",
        ),
        (
            "see <https://doc.rust-lang.org/nightly/rustc/check-cfg.html> for more information about checking conditional configuration",
            "see the Trust trustc check-cfg documentation for more information about checking conditional configuration",
        ),
        (
            "visit <https://doc.rust-lang.org/nightly/rustc/check-cfg.html> for more details",
            "visit the Trust trustc check-cfg documentation for more details",
        ),
        (
            "see <https://doc.rust-lang.org/nightly/rustc/check-cfg/cargo-specifics.html> for more information about checking conditional configuration",
            "see the Trust trustc check-cfg Cargo documentation for more information about checking conditional configuration",
        ),
        (
            "to learn more about uninhabited types, see https://doc.rust-lang.org/nomicon/exotic-sizes.html#empty-types",
            "to learn more about uninhabited types, see the Trust Nomicon's empty types section",
        ),
        (
            "for more details on interior mutability see <https://doc.rust-lang.org/reference/interior-mutability.html>",
            "for more details on interior mutability, see the Trust Reference's interior mutability section",
        ),
        (
            "for more information, see <https://doc.rust-lang.org/reference/patterns.html#binding-modes>",
            "for more information, see the Trust Reference's pattern binding modes section",
        ),
        (
            "function calls are not allowed in patterns: <https://doc.rust-lang.org/book/ch19-00-patterns.html>",
            "function calls are not allowed in patterns; see the Trust Book's patterns chapter",
        ),
        (
            "arbitrary expressions are not allowed in patterns: <https://doc.rust-lang.org/book/ch19-00-patterns.html>",
            "arbitrary expressions are not allowed in patterns; see the Trust Book's patterns chapter",
        ),
        (
            "for more information, visit https://doc.rust-lang.org/book/ch19-00-patterns.html",
            "for more information, see the Trust Book's patterns chapter",
        ),
        (
            "see <https://doc.rust-lang.org/nightly/reference/macros-by-example.html#forwarding-a-matched-fragment> for more information",
            "see the Trust Reference's macro fragment forwarding section for more information",
        ),
        (
            "for information about formatting flags, visit https://doc.rust-lang.org/std/fmt/index.html",
            "for information about formatting flags, see the Trust standard library formatting documentation",
        ),
        (
            "for more information, visit https://doc.rust-lang.org/book/ch19-02-refutability.html",
            "for more information, see the Trust Book's refutability section",
        ),
        (
            "for more information, see <https://doc.rust-lang.org/reference/destructors.html>",
            "for more information, see the Trust Reference's destructors section",
        ),
        (
            "for more information, visit <https://doc.rust-lang.org/book/ch15-05-interior-mutability.html>",
            "for more information, see the Trust Book's interior mutability chapter",
        ),
        (
            "for more information, visit <https://doc.rust-lang.org/std/ptr/index.html> and <https://doc.rust-lang.org/reference/behavior-considered-undefined.html>",
            "for more information, see the Trust standard library pointer docs and the Trust Reference's undefined behavior section",
        ),
        (
            "for more information on higher-ranked polymorphism, visit https://doc.rust-lang.org/nomicon/hrtb.html",
            "for more information on higher-ranked polymorphism, see the Trust Nomicon's higher-ranked trait bounds section",
        ),
        (
            "see <https://doc.rust-lang.org/nomicon/subtyping.html> for more information about variance",
            "see the Trust Nomicon's subtyping section for more information about variance",
        ),
        (
            "for more information visit <https://doc.rust-lang.org/nightly/core/ptr/fn.fn_addr_eq.html>",
            "for more information, see the Trust core pointer documentation for `fn_addr_eq`",
        ),
        (
            "for more information see https://doc.rust-lang.org/reference/items/implementations.html#orphan-rules",
            "for more information, see the Trust Reference's orphan rules section",
        ),
        (
            "for more details about the orphan rules, see <https://doc.rust-lang.org/reference/items/implementations.html?highlight=orphan#orphan-rules>",
            "for more details about the orphan rules, see the Trust Reference's orphan rules section",
        ),
        (
            "for more information, visit https://doc.rust-lang.org/std/keyword.extern.html",
            "for more information, see the Trust standard library `extern` keyword documentation",
        ),
        (
            "for more on editions, read https://doc.rust-lang.org/edition-guide",
            "for more on editions, read the Trust Edition Guide",
        ),
        (
            "see https://doc.rust-lang.org/stable/std/array/fn.from_fn.html for more information",
            "see the Trust standard library array `from_fn` documentation for more information",
        ),
        (
            "use the `cargo:rustc-link-lib` directive to specify the native libraries to link with Cargo (see https://doc.rust-lang.org/cargo/reference/build-scripts.html#rustc-link-lib)",
            "use the `cargo:rustc-link-lib` directive to specify the native libraries to link with targo-compatible build scripts; see the Trust Cargo build script documentation for that directive",
        ),
        (
            "for more information see https://doc.rust-lang.org/reference/types/numeric.html#machine-dependent-integer-types",
            "for more information, see the Trust Reference's machine-dependent integer types section",
        ),
        (
            "see https://doc.rust-lang.org/stable/std/process/struct.Child.html#warning",
            "see the Trust standard library process `Child` documentation for more information",
        ),
        (
            "see also https://doc.rust-lang.org/nightly/nightly-rustc/?search=diag&filter-crate=clippy_utils",
            "see also the Trust nightly compiler internals documentation for `diag`",
        ),
        (
            "see also https://doc.rust-lang.org/nightly/nightly-rustc/?search=lang&filter-crate=clippy_utils",
            "see also the Trust nightly compiler internals documentation for `lang`",
        ),
        (
            "for more information about transmute, see <https://doc.rust-lang.org/std/mem/fn.transmute.html#transmutation-between-pointers-and-integers>",
            "for more information about transmute, see the Trust standard library transmute documentation",
        ),
        (
            "for more information, see https://doc.rust-lang.org/std/mem/fn.transmute.html",
            "for more information, see the Trust standard library transmute documentation",
        ),
        (
            "for more information about exposed provenance, see <https://doc.rust-lang.org/std/ptr/index.html#exposed-provenance>",
            "for more information about exposed provenance, see the Trust standard library pointer documentation",
        ),
        (
            "see <https://doc.rust-lang.org/book/ch05-01-defining-structs.html> for more information",
            "see the Trust Book's defining structs section for more information",
        ),
        (
            "see https://doc.rust-lang.org/book/ch05-03-method-syntax.html for more information",
            "see the Trust Book's method syntax section for more information",
        ),
        (
            "this error was originally ignored because you are running `rustdoc`",
            "this error was originally ignored because you are running `trustdoc`",
        ),
        (
            "try running again with `rustc` or `cargo check` and you may get a more detailed error",
            "try running again with `trustc` or `targo trust check` and you may get a more detailed error",
        ),
        ("exists in `rustc` lints", "exists in `trustc` lints"),
        ("Compilation failed, aborting rustdoc", "Compilation failed, aborting trustdoc"),
    ] {
        next = next.replace(from, to);
    }
    if next.contains("pass `--edition ") {
        next = next.replace(" to `rustc`", " to `trustc`");
    }

    // `see issue #N <https://github.com/rust-lang/rust/issues/N>` notes are
    // kept verbatim: the compiler emits the URL, so stripping it from the
    // expected text manufactured ~37 spurious stderr mismatches. The old
    // `issue_112792_url_policy` rule (and its per-issue loop here) is retired.

    next
}

fn replace_error_code_urls(line: &str) -> String {
    let mut output = String::new();
    let mut remaining = line;
    let needle = "https://doc.rust-lang.org/error_codes/";
    while let Some(start) = remaining.find(needle) {
        output.push_str(&remaining[..start]);
        let after = &remaining[start + needle.len()..];
        if let Some(code) = after.strip_prefix('E').and_then(|rest| rest.split_once(".html")) {
            let code_id = format!("E{}", code.0);
            if code_id[1..].bytes().all(|byte| byte.is_ascii_digit()) {
                output.push_str(
                    "https://github.com/alabsystems/Trust/blob/main/compiler/rustc_error_codes/src/error_codes/",
                );
                output.push_str(&code_id);
                output.push_str(".md");
                remaining = code.1;
                continue;
            }
        }
        output.push_str(needle);
        remaining = after;
    }
    output.push_str(remaining);
    output
}

fn write_audit_markdown(path: &Path, audit: &[AuditRecord]) -> Result<(), PortError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut by_rule = BTreeMap::<&str, usize>::new();
    let mut touched = BTreeSet::<&str>::new();
    for row in audit {
        *by_rule.entry(&row.rule).or_default() += 1;
        touched.insert(&row.path);
    }

    let mut output = String::new();
    pushln(&mut output, format_args!("# Upstream Test Porting Audit"));
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("Modified files: {}", touched.len()));
    pushln(&mut output, format_args!("Audit records: {}", audit.len()));
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Rule Counts"));
    pushln(&mut output, format_args!(""));
    for (rule, count) in by_rule {
        pushln(&mut output, format_args!("- {rule}: {count}"));
    }
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Line Edits"));
    pushln(&mut output, format_args!(""));
    for row in audit {
        if row.rule == "file_digest" {
            continue;
        }
        let line = row.line.unwrap_or_default();
        pushln(&mut output, format_args!("- {}:{} `{}`", row.path, line, row.rule));
        if let Some(before) = &row.before {
            pushln(&mut output, format_args!("  - before: {}", markdown_inline_code(before)));
        }
        if let Some(after) = &row.after {
            pushln(&mut output, format_args!("  - after: {}", markdown_inline_code(after)));
        }
    }
    fs::write(path, output)?;
    Ok(())
}

fn markdown_inline_code(value: &str) -> String {
    let mut fence = "`".to_string();
    while value.contains(&fence) {
        fence.push('`');
    }
    format!("{fence}{value}{fence}")
}

fn parse_baseline_document(path: &Path) -> Result<CompatibilityBaseline, PortError> {
    let input = fs::read_to_string(path)?;
    match document_format(path) {
        DocumentFormat::Json => Ok(parse_baseline_json(&input)?),
        DocumentFormat::Toml => Ok(parse_baseline_toml(&input)?),
    }
}

fn read_upstream_fix_ledger(path: &Path) -> Result<Value, PortError> {
    if !path.exists() {
        return Ok(json!({
            "path": path.to_string_lossy(),
            "present": false,
            "tracked_until_revision": null,
            "fixes_count": 0,
            "fix_ids": [],
            "status_counts": {},
            "local_action_counts": {},
            "pending_local_actions_count": 0,
            "pending_local_actions": [],
        }));
    }
    let input = fs::read_to_string(path)?;
    let ledger: UpstreamFixLedger = match document_format(path) {
        DocumentFormat::Json => parse_upstream_fixes_json(&input)?,
        DocumentFormat::Toml => parse_upstream_fixes_toml(&input)?,
    };
    let mut status_counts = BTreeMap::<String, usize>::new();
    let mut action_counts = BTreeMap::<String, usize>::new();
    let mut fix_ids = Vec::new();
    let mut pending = Vec::new();
    for fix in &ledger.fixes {
        fix_ids.push(fix.id.clone());
        *status_counts.entry(upstream_fix_status_label(fix.status).to_string()).or_default() += 1;
        let action = local_fix_action_label(fix.local_action);
        *action_counts.entry(action.to_string()).or_default() += 1;
        if PENDING_LOCAL_FIX_ACTIONS.contains(&fix.local_action) {
            pending.push(json!({
                "id": fix.id,
                "baseline_entry_id": fix.baseline_entry_id,
                "title": fix.title,
                "upstream_reference": fix.upstream_reference,
                "local_action": action,
                "landed_in_revision": fix.landed_in_revision,
            }));
        }
    }
    Ok(json!({
        "path": path.to_string_lossy(),
        "present": true,
        "tracked_until_revision": ledger.tracked_until_revision,
        "fixes_count": ledger.fixes.len(),
        "fix_ids": fix_ids,
        "status_counts": status_counts,
        "local_action_counts": action_counts,
        "pending_local_actions_count": pending.len(),
        "pending_local_actions": pending,
    }))
}

fn upstream_fix_status_label(status: UpstreamFixStatus) -> &'static str {
    match status {
        UpstreamFixStatus::Proposed => "proposed",
        UpstreamFixStatus::Landed => "landed",
        UpstreamFixStatus::Released => "released",
        UpstreamFixStatus::Backported => "backported",
        UpstreamFixStatus::Reverted => "reverted",
    }
}

fn local_fix_action_label(action: LocalFixAction) -> &'static str {
    match action {
        LocalFixAction::NoneNeeded => "none_needed",
        LocalFixAction::RebaseBaseline => "rebase_baseline",
        LocalFixAction::CherryPick => "cherry_pick",
        LocalFixAction::PortFix => "port_fix",
        LocalFixAction::DropException => "drop_exception",
        LocalFixAction::TrackOnly => "track_only",
    }
}

fn test_exception_accounting(
    test_exceptions: &TestExceptionLedger,
    validation_date: &str,
) -> Value {
    let mut status_counts = BTreeMap::<String, usize>::new();
    let mut kind_counts = BTreeMap::<String, usize>::new();
    let mut active = Vec::new();
    let mut active_intentional_divergences = Vec::new();

    for exception in &test_exceptions.exceptions {
        *status_counts.entry(exception_status_label(exception.status).to_string()).or_default() +=
            1;
        *kind_counts.entry(test_exception_kind_label(exception.kind).to_string()).or_default() += 1;
        if exception.status == ExceptionStatus::Active {
            let row = json!({
                "id": exception.id,
                "test_id": exception.test_id,
                "suite": exception.suite,
                "path": exception.path,
                "revision": exception.revision,
                "kind": test_exception_kind_label(exception.kind),
                "owner": exception.owner,
                "reason": exception.reason,
                "issue": exception.issue,
                "reviewed_on": exception.reviewed_on,
                "expires_on": exception.expires_on,
            });
            if exception.kind == TestExceptionKind::IntentionalDivergence {
                active_intentional_divergences.push(row.clone());
            }
            active.push(row);
        }
    }

    json!({
        "schema_version": test_exceptions.schema_version,
        "validation_date": validation_date,
        "total_exceptions": test_exceptions.exceptions.len(),
        "active_exception_count": active.len(),
        "active_intentional_divergence_count": active_intentional_divergences.len(),
        "status_counts": status_counts,
        "kind_counts": kind_counts,
        "active_exceptions": active,
        "active_intentional_divergences": active_intentional_divergences,
    })
}

fn exception_status_label(status: ExceptionStatus) -> &'static str {
    match status {
        ExceptionStatus::Active => "active",
        ExceptionStatus::Expired => "expired",
        ExceptionStatus::Resolved => "resolved",
    }
}

fn test_exception_kind_label(kind: TestExceptionKind) -> &'static str {
    match kind {
        TestExceptionKind::ExpectedFail => "expected_fail",
        TestExceptionKind::ExpectedSkip => "expected_skip",
        TestExceptionKind::ChangedDiagnostic => "changed_diagnostic",
        TestExceptionKind::IntentionalDivergence => "intentional_divergence",
        TestExceptionKind::EnvironmentalSkip => "environmental_skip",
    }
}

fn revision_drift(
    baseline_revision: Option<&str>,
    requested_revision: &str,
    resolved_revision: &str,
    upstream_remote: &str,
    resolution_source: &str,
) -> Value {
    let baseline = baseline_revision.map(|revision| revision_ref(revision).trim().to_string());
    let requested = requested_revision.trim();
    let requested_ref = revision_ref(requested_revision).trim();
    let resolved = revision_ref(resolved_revision).trim();
    let comparable =
        baseline.as_deref().is_some_and(|value| !value.is_empty()) && !resolved.is_empty();
    let drifted = comparable && baseline.as_deref() != Some(resolved);
    json!({
        "baseline_revision": baseline,
        "baseline_revision_present": baseline_revision.is_some_and(|value| !value.is_empty()),
        "requested_revision": requested,
        "requested_ref": requested_ref,
        "requested_qualifier": revision_qualifier(requested_revision),
        "upstream_remote": upstream_remote,
        "resolved_revision": resolved,
        "resolution_source": resolution_source,
        "can_compare_to_baseline": comparable,
        "drifted_from_baseline": drifted,
        "requires_upstream_fix_review": drifted || !comparable,
        "default_reviewed_upstream_request": requested == DEFAULT_REVIEWED_UPSTREAM_REVISION && upstream_remote == DEFAULT_UPSTREAM_REMOTE,
        "default_latest_upstream_request": requested == LATEST_UPSTREAM_REVISION_REQUEST && upstream_remote == DEFAULT_UPSTREAM_REMOTE,
    })
}

fn upstream_fix_accounting(
    ledger: &Value,
    baseline_revision: Option<&str>,
    resolved_revision: &str,
) -> Value {
    let baseline = baseline_revision.map(|revision| revision_ref(revision).trim().to_string());
    let current = revision_ref(resolved_revision).trim().to_string();
    let tracked = ledger
        .get("tracked_until_revision")
        .and_then(Value::as_str)
        .map(|revision| revision_ref(revision).trim().to_string());
    let drifted = baseline.as_deref().is_some_and(|base| base != current);
    let ledger_present = ledger.get("present").and_then(Value::as_bool).unwrap_or(false);
    let reviewed = ledger_present && (!drifted || tracked.as_deref() == Some(current.as_str()));
    let pending_count =
        ledger.get("pending_local_actions_count").and_then(Value::as_u64).unwrap_or(0);
    let claim = if !ledger_present {
        "upstream fix ledger is missing"
    } else if !drifted {
        "post-baseline upstream range is empty"
    } else if reviewed && pending_count > 0 {
        "ledger reviewed through current upstream revision with pending local actions"
    } else if reviewed {
        "ledger reviewed through current upstream revision"
    } else {
        "current upstream revision has unreviewed post-baseline range"
    };
    json!({
        "ledger_path": ledger.get("path").cloned().unwrap_or(Value::Null),
        "ledger_present": ledger_present,
        "fixes_count": ledger.get("fixes_count").cloned().unwrap_or_else(|| json!(0)),
        "fix_ids": ledger.get("fix_ids").cloned().unwrap_or_else(|| json!([])),
        "status_counts": ledger.get("status_counts").cloned().unwrap_or_else(|| json!({})),
        "local_action_counts": ledger.get("local_action_counts").cloned().unwrap_or_else(|| json!({})),
        "pending_local_actions_count": pending_count,
        "pending_local_actions": ledger.get("pending_local_actions").cloned().unwrap_or_else(|| json!([])),
        "tracked_until_revision": tracked,
        "baseline_revision": baseline,
        "current_revision": current,
        "reviewed_through_current_revision": reviewed,
        "unreviewed_revision_drift": drifted && !reviewed,
        "applicable_fix_tracking_claim": claim,
    })
}

fn current_test_files(root: &Path) -> Result<BTreeSet<String>, PortError> {
    let output = git(root, &["ls-files", "--cached", "--others", "--exclude-standard", "tests"])?;
    Ok(output
        .lines()
        .filter(|line| line.starts_with(UPSTREAM_TEST_PREFIX))
        .map(str::to_string)
        .collect())
}

fn apply_ported_overlay(
    root: &Path,
    ported: &Path,
    paths: &[String],
    stale_paths: &[String],
) -> Result<(Vec<String>, Vec<String>), PortError> {
    let current_upstream_paths = paths.iter().cloned().collect::<BTreeSet<_>>();
    let stale_upstream_paths = stale_paths.iter().cloned().collect::<BTreeSet<_>>();
    let dirty = git(root, &["status", "--porcelain=v1", "--", "tests"])?;
    let blocking_dirty = dirty
        .lines()
        .flat_map(git_status_porcelain_paths)
        .filter(|path| current_upstream_paths.contains(path) || stale_upstream_paths.contains(path))
        .collect::<BTreeSet<_>>();
    if !blocking_dirty.is_empty() {
        return Err(PortError::Message(format!(
            "refusing to apply ported tests with dirty upstream-owned test paths: {}",
            blocking_dirty.into_iter().take(20).collect::<Vec<_>>().join(", ")
        )));
    }

    let tests_root = root.join("tests");
    let mut removed_stale = Vec::new();
    for rel in stale_paths {
        if current_upstream_paths.contains(rel) || !rel.starts_with(UPSTREAM_TEST_PREFIX) {
            continue;
        }
        let target = root.join(rel);
        if !target.exists() {
            continue;
        }
        if target.is_dir() {
            return Err(PortError::Message(format!(
                "refusing to remove stale upstream directory path: {rel}"
            )));
        }
        fs::remove_file(&target)?;
        prune_empty_parents(&target, &tests_root)?;
        removed_stale.push(rel.clone());
    }

    let mut applied = Vec::new();
    for rel in paths {
        let source = ported.join(rel);
        if !source.exists() {
            continue;
        }
        let target = root.join(rel);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::copy(source, target)?;
        applied.push(rel.clone());
    }
    Ok((applied, removed_stale))
}

fn git_status_porcelain_paths(line: &str) -> Vec<String> {
    let Some(rest) = line.get(3..) else {
        return Vec::new();
    };
    rest.split(" -> ").map(unquote_git_status_path).collect()
}

fn unquote_git_status_path(path: &str) -> String {
    let trimmed = path.trim();
    if trimmed.len() >= 2 && trimmed.starts_with('"') && trimmed.ends_with('"') {
        trimmed[1..trimmed.len() - 1].to_string()
    } else {
        trimmed.to_string()
    }
}

fn prune_empty_parents(path: &Path, stop: &Path) -> Result<(), PortError> {
    let mut parent = path.parent();
    while let Some(dir) = parent {
        if dir == stop || dir.parent().is_none() {
            break;
        }
        match fs::remove_dir(dir) {
            Ok(()) => parent = dir.parent(),
            Err(error) if error.kind() == io::ErrorKind::DirectoryNotEmpty => break,
            Err(error) if error.kind() == io::ErrorKind::NotFound => break,
            Err(error) => return Err(error.into()),
        }
    }
    Ok(())
}

fn primary_compiletest_path(path: &str) -> Option<String> {
    if !COMPILETEST_PREFIXES.iter().any(|prefix| path.starts_with(prefix)) {
        return None;
    }
    if path.starts_with("tests/run-make/") {
        let mut parts = path.split('/');
        let a = parts.next()?;
        let b = parts.next()?;
        let c = parts.next()?;
        return Some(format!("{a}/{b}/{c}"));
    }
    PRIMARY_SUFFIXES.iter().any(|suffix| path.ends_with(suffix)).then(|| path.to_string())
}

fn unique_primary_paths(paths: &[String]) -> Vec<String> {
    paths
        .iter()
        .filter_map(|path| primary_compiletest_path(path))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

// Trust: `test_exceptions`/`validation_date` let raw-scraped test failures be
// netted against an active, non-expired, Failed-accounting exception — the same
// consistency the proof bundle already applies (matching_test_exception_id). A
// reviewed `intentional_divergence` (e.g. tests/crashes/135122.rs: tRust emits
// ordinary diagnostics where upstream ICEs) is Trust being SUPERIOR, not a
// regression, so it must not inflate totals.failed. Netted failures stay LISTED
// in failed_tests with `excepted: true` + `exception_id` (transparent, not hidden).
fn parse_scorecard(
    log_path: &Path,
    test_exceptions: &TestExceptionLedger,
    validation_date: &str,
) -> Result<Value, PortError> {
    if !log_path.exists() {
        return Ok(json!({
            "executed": false,
            "exit_status": null,
            "failed_tests": [],
            "tool_failures": [],
            "totals": {"failed": 0, "tool_failures": 0, "categories": {}},
        }));
    }

    let text = fs::read_to_string(log_path)?;
    let lines = text.lines().map(str::to_string).collect::<Vec<_>>();
    let mut failures = BTreeMap::<String, Value>::new();
    for (line_index, line) in lines.iter().enumerate() {
        if let Some((suite, path)) = parse_compiletest_fail_line(line) {
            add_failure(&mut failures, suite, path, line_index + 1, &text);
        }
        if let Some((suite, path)) = parse_failure_list_line(line) {
            add_failure(&mut failures, suite, path, line_index + 1, &text);
        }
    }

    for (idx, line) in lines.iter().enumerate() {
        let Some((suite, path)) = parse_block_header(line) else {
            continue;
        };
        let block_start = idx + 1;
        let mut block_end = lines.len();
        let end_marker = format!("---- [{suite}] {path} stdout end ----");
        for (end_idx, candidate) in lines.iter().enumerate().skip(idx + 1) {
            if candidate == &end_marker {
                block_end = end_idx + 1;
                break;
            }
        }
        let block_text = lines[idx..block_end].join("\n");
        let key = failure_key(suite, path);
        add_failure(&mut failures, suite, path, block_start, &block_text);
        if let Some(failure) = failures.get_mut(&key) {
            merge_failure_detail(failure, &lines, block_start, block_end);
        }
    }

    let mut tool_failures = Vec::new();
    let mut seen_tool_keys = BTreeSet::new();
    for (idx, line) in lines.iter().enumerate() {
        let line_number = idx + 1;
        if let Some(crate_name) = parse_cargo_compile_failure(line)
            && seen_tool_keys.insert(format!("cargo-compile:{line_number}"))
        {
            tool_failures.push(json!({
                "kind": "cargo-compile",
                "crate": crate_name,
                "message": line,
                "line": line_number,
                "failure_snippet": around_line_snippet(&lines, line_number),
            }));
        }
        if line.starts_with("tidy [")
            && line.ends_with("]: FAIL")
            && seen_tool_keys.insert(format!("tidy:{line_number}"))
        {
            let crate_name = line.trim_end_matches(": FAIL");
            tool_failures.push(json!({
                "kind": "tidy",
                "crate": crate_name,
                "message": line,
                "line": line_number,
                "failure_snippet": around_line_snippet(&lines, line_number),
            }));
        }
    }

    let mut categories = BTreeMap::<String, usize>::new();
    let mut excepted = 0usize;
    for failure in failures.values_mut() {
        let suite = failure.get("suite").and_then(Value::as_str).unwrap_or("").to_string();
        let path = failure.get("path").and_then(Value::as_str).unwrap_or("").to_string();
        // Trust: net a failure covered by an active, non-expired exception whose
        // kind accounts for a Failed outcome; keep it listed but out of the count.
        if let Some(exception_id) =
            failure_covering_exception(test_exceptions, &suite, &path, validation_date)
        {
            set_object_field(failure, "excepted", json!(true));
            set_object_field(failure, "exception_id", json!(exception_id));
            excepted += 1;
            continue;
        }
        let category = failure.get("category").and_then(Value::as_str).unwrap_or("unknown");
        *categories.entry(category.to_string()).or_default() += 1;
    }

    Ok(json!({
        "executed": true,
        "failed_tests": failures.into_values().collect::<Vec<_>>(),
        "tool_failures": tool_failures,
        "totals": {
            "failed": categories.values().sum::<usize>(),
            "excepted": excepted,
            "tool_failures": tool_failures.len(),
            "categories": categories,
        },
    }))
}

// Trust: find an ACTIVE, non-expired test exception whose kind accounts for a
// Failed outcome and whose (suite, path) matches this scraped failure. Returns
// the exception id to record on the netted failure. Mirrors the active-status +
// kind-accounts-for logic already used for the proof bundle
// (matching_test_exception_id), but keys on (suite, path) since scraped failures
// carry no inventory test_id. Expiry is enforced (expires_on >= validation_date,
// YYYY-MM-DD lexicographic == chronological) so a lapsed exception cannot net.
fn failure_covering_exception(
    test_exceptions: &TestExceptionLedger,
    suite: &str,
    path: &str,
    validation_date: &str,
) -> Option<String> {
    test_exceptions
        .exceptions
        .iter()
        .find(|exception| {
            exception.status == ExceptionStatus::Active
                && exception.suite == suite
                && exception.path == path
                && exception.expires_on.as_str() >= validation_date
                && test_exception_kind_accounts_for(TestOutcome::Failed, exception.kind)
        })
        .map(|exception| exception.id.clone())
}

fn parse_compiletest_fail_line(line: &str) -> Option<(&str, &str)> {
    if !line.ends_with(" ... F") || !line.starts_with('[') {
        return None;
    }
    let (suite, rest) = line[1..].split_once("] ")?;
    let path = rest.strip_suffix(" ... F")?;
    path.starts_with("tests/").then_some((suite, path))
}

fn parse_failure_list_line(line: &str) -> Option<(&str, &str)> {
    let trimmed = line.trim_start();
    if !trimmed.starts_with('[') || !line.starts_with("    ") {
        return None;
    }
    let (suite, path) = trimmed[1..].split_once("] ")?;
    path.starts_with("tests/").then_some((suite, path))
}

fn parse_block_header(line: &str) -> Option<(&str, &str)> {
    let body = line.strip_prefix("---- [")?.strip_suffix(" stdout ----")?;
    let (suite, path) = body.split_once("] ")?;
    path.starts_with("tests/").then_some((suite, path))
}

fn parse_cargo_compile_failure(line: &str) -> Option<&str> {
    line.strip_prefix("error: could not compile `")?.split_once('`').map(|(name, _)| name)
}

fn failure_key(suite: &str, path: &str) -> String {
    format!("[{suite}] {path}")
}

fn add_failure<'a>(
    failures: &'a mut BTreeMap<String, Value>,
    suite: &str,
    path: &str,
    line_number: usize,
    log_text: &str,
) -> &'a mut Value {
    let key = failure_key(suite, path);
    failures.entry(key).or_insert_with(|| {
        json!({
            "suite": suite,
            "path": path,
            "category": category_for_failure(path, log_text),
            "first_seen_line": line_number,
            "listed_lines": [],
            "actual_artifacts": [],
            "comparisons": [],
            "expected_references": [],
            "detail_available": false,
        })
    });
    let failure = failures.get_mut(&failure_key(suite, path)).expect("inserted");
    if let Some(lines) = failure.get_mut("listed_lines").and_then(Value::as_array_mut) {
        lines.push(json!(line_number));
    }
    failure
}

fn category_for_failure(path: &str, log_text: &str) -> &'static str {
    if path.starts_with("tests/ui-fulldeps/") {
        "rustc-private-or-fulldeps-drift"
    } else if path.starts_with("tests/rustdoc") {
        "rustdoc-output-drift"
    } else if path.starts_with("tests/codegen") || path.starts_with("tests/assembly") {
        "codegen-output-drift"
    } else if path.starts_with("tests/crashes/") {
        "crash-status-drift"
    } else if path.starts_with("tests/debuginfo/") {
        "debuginfo-debugger-output-drift"
    } else if path.contains("/contracts/") {
        "trust-contract-drift"
    } else if path.contains("terminal_urls") {
        "terminal-url-drift"
    } else if path == "tests/ui/compile-flags/invalid/print.rs"
        || path == "tests/ui/print-request/print-lints-help.rs"
        || path.starts_with("tests/ui/pattern/usefulness/")
    {
        "documentation-diagnostic-drift"
    } else if path.starts_with("tests/ui/diagnostic-width/")
        || path.contains("too-many-hash")
        || path.contains("nonfatal-parsing")
    {
        "diagnostic-rendering-drift"
    } else if log_text.contains("The actual stderr differed") {
        "diagnostic-drift"
    } else if log_text.contains("The actual ") && log_text.contains(" differed from the expected ")
    {
        "expected-output-drift"
    } else if log_text.contains("test compilation failed") {
        "compile-failure"
    } else if log_text.contains("test did not exit with success") {
        "runtime-failure"
    } else {
        "behavior-or-diagnostic-drift"
    }
}

fn merge_failure_detail(
    failure: &mut Value,
    lines: &[String],
    block_start: usize,
    block_end: usize,
) {
    let block_lines = &lines[block_start - 1..block_end];
    let details = extract_failure_details(block_lines, block_start);
    let block_text = block_lines.join("\n");
    set_object_field(failure, "detail_available", json!(true));
    set_object_field(failure, "detail_start_line", json!(block_start));
    set_object_field(failure, "detail_end_line", json!(block_end));
    set_object_field(failure, "failure_snippet", log_snippet(lines, block_start, block_end));
    let path = failure.get("path").and_then(Value::as_str).unwrap_or_default().to_string();
    set_object_field(failure, "category", json!(category_for_failure(&path, &block_text)));
    extend_array_field(failure, "actual_artifacts", details["actual_artifacts"].clone());
    extend_array_field(failure, "comparisons", details["comparisons"].clone());
    extend_array_field(failure, "expected_references", details["expected_references"].clone());
    if !details["input_artifact"].is_null() {
        set_object_field(failure, "input_artifact", details["input_artifact"].clone());
    }
    if !details["check_artifact"].is_null() {
        set_object_field(failure, "check_artifact", details["check_artifact"].clone());
    }
}

fn extend_array_field(object: &mut Value, key: &str, values: Value) {
    let Some(values) = values.as_array() else {
        return;
    };
    if let Some(target) = object.get_mut(key).and_then(Value::as_array_mut) {
        target.extend(values.iter().cloned());
    }
}

fn extract_failure_details(block_lines: &[String], start_line: usize) -> Value {
    let mut artifacts = Vec::new();
    let mut comparisons = Vec::new();
    let mut expected_references = Vec::new();
    let mut diff_kind: Option<String> = None;
    let mut diff_start = 0usize;
    let mut diff_excerpt = Vec::<String>::new();
    let mut input_artifact = None::<String>;
    let mut check_artifact = None::<String>;

    for (offset, line) in block_lines.iter().enumerate() {
        let line_number = start_line + offset;
        if let Some(rest) = line.strip_prefix("Saved the actual ")
            && let Some((kind, tail)) = rest.split_once(" to `")
            && let Some((path, _)) = tail.split_once('`')
        {
            artifacts.push(json!({"kind": kind, "path": path, "line": line_number}));
        }
        if let Some(rest) = line.strip_prefix("The actual ")
            && let Some((actual, tail)) = rest.split_once(" differed from the expected ")
        {
            let expected = tail.split_whitespace().next().unwrap_or(tail);
            comparisons.push(json!({
                "actual": actual,
                "expected": expected,
                "line": line_number,
                "message": line,
            }));
        }
        if let Some(kind) = line.strip_prefix("diff of ").and_then(|rest| rest.strip_suffix(':')) {
            diff_kind = Some(kind.to_string());
            diff_start = line_number;
            diff_excerpt.clear();
            continue;
        }
        if let Some(kind) = diff_kind.as_ref() {
            if (line.starts_with('+') || line.starts_with('-') || line.starts_with(' '))
                && diff_excerpt.len() < 80
            {
                diff_excerpt.push(line.clone());
            } else if !diff_excerpt.is_empty() {
                comparisons.push(json!({
                    "actual": kind,
                    "expected": kind,
                    "line": diff_start,
                    "message": format!("diff of {kind}"),
                    "diff_excerpt": diff_excerpt.join("\n").trim_end(),
                }));
                diff_kind = None;
                diff_excerpt.clear();
            }
        }
        if let Some(path) = line.strip_prefix("Input file: ") {
            input_artifact = Some(path.to_string());
            artifacts.push(json!({"kind": "filecheck-input", "path": path, "line": line_number}));
        }
        if let Some(path) = line.strip_prefix("Check file: ") {
            check_artifact = Some(path.to_string());
            expected_references.push(json!({
                "kind": "filecheck-check-file",
                "path": path,
                "line": line_number,
            }));
        }
        if line.contains("//@") {
            expected_references.push(json!({
                "kind": "compiletest-directive",
                "line": line_number,
                "text": line.trim(),
            }));
        }
        if line.starts_with("To update references") {
            expected_references.push(json!({
                "kind": "bless-hint",
                "line": line_number,
                "text": line,
            }));
        }
        if line.starts_with("To only update this specific test") {
            expected_references.push(json!({
                "kind": "targeted-bless-hint",
                "line": line_number,
                "text": line,
            }));
        }
    }

    if let Some(kind) = diff_kind
        && !diff_excerpt.is_empty()
    {
        comparisons.push(json!({
            "actual": kind,
            "expected": kind,
            "line": diff_start,
            "message": format!("diff of {kind}"),
            "diff_excerpt": diff_excerpt.join("\n").trim_end(),
        }));
    }

    json!({
        "actual_artifacts": artifacts,
        "comparisons": comparisons,
        "expected_references": expected_references,
        "input_artifact": input_artifact,
        "check_artifact": check_artifact,
    })
}

fn log_snippet(lines: &[String], start: usize, end: usize) -> Value {
    let bounded_end = std::cmp::min(end, start + 79);
    json!({
        "start_line": start,
        "end_line": bounded_end,
        "truncated": bounded_end < end,
        "text": lines[start - 1..bounded_end].join("\n"),
    })
}

fn around_line_snippet(lines: &[String], line_number: usize) -> Value {
    let start = line_number.saturating_sub(20).max(1);
    let end = std::cmp::min(lines.len(), line_number + 5);
    json!({
        "start_line": start,
        "end_line": end,
        "truncated": start > 1 || end < lines.len(),
        "text": lines[start - 1..end].join("\n"),
    })
}

fn scorecard_validation_failures(scorecard: &Value) -> Vec<Value> {
    let mut failures = Vec::new();
    let baseline = scorecard.get("baseline_revision").and_then(Value::as_str);
    if baseline.is_none_or(str::is_empty) {
        failures.push(json!({
            "kind": "missing-upstream-baseline-revision",
            "message": "cannot account for latest upstream drift without a baseline upstream revision",
        }));
    }
    let Some(accounting) = scorecard.get("upstream_fix_accounting").and_then(Value::as_object)
    else {
        failures.push(json!({
            "kind": "missing-upstream-fix-accounting",
            "message": "cannot validate upstream fix accounting without ledger metadata",
        }));
        return failures;
    };
    if !accounting.get("ledger_present").and_then(Value::as_bool).unwrap_or(false) {
        failures.push(json!({
            "kind": "missing-upstream-fix-ledger",
            "message": format!(
                "upstream fix ledger is missing: {}",
                accounting.get("ledger_path").unwrap_or(&Value::Null)
            ),
        }));
    }
    if accounting.get("unreviewed_revision_drift").and_then(Value::as_bool).unwrap_or(false) {
        failures.push(json!({
            "kind": "unreviewed-upstream-revision-drift",
            "message": format!(
                "resolved upstream revision {} is newer than reviewed ledger revision {}",
                accounting.get("current_revision").and_then(Value::as_str).unwrap_or("unknown"),
                accounting.get("tracked_until_revision").and_then(Value::as_str).unwrap_or("unknown"),
            ),
            "baseline_revision": accounting.get("baseline_revision").cloned().unwrap_or(Value::Null),
            "tracked_until_revision": accounting.get("tracked_until_revision").cloned().unwrap_or(Value::Null),
            "current_revision": accounting.get("current_revision").cloned().unwrap_or(Value::Null),
            "ledger_path": accounting.get("ledger_path").cloned().unwrap_or(Value::Null),
        }));
    }
    failures
}

fn scorecard_exit_code(
    scorecard: &Value,
    execute: bool,
    execution_exit_status: Option<i32>,
    validation_failures: &[Value],
) -> u8 {
    if !validation_failures.is_empty() {
        return 1;
    }
    if execute {
        match execution_exit_status {
            Some(0) => {}
            Some(_) | None => return 1,
        }
    }
    if scorecard_total(scorecard, "failed") != 0 {
        return 1;
    }
    if scorecard_total(scorecard, "tool_failures") != 0 {
        return 1;
    }
    0
}

fn porting_exit_code(scorecard: &Value, execute: bool, proof_mode: ProofMode) -> u8 {
    if scorecard_total(scorecard, "failed") != 0 || scorecard_total(scorecard, "tool_failures") != 0
    {
        return 1;
    }
    if !execute {
        return 0;
    }
    if proof_required_for_exit(execute, proof_mode) {
        let exit_status = scorecard.get("execution_exit_status").and_then(Value::as_i64);
        if !matches!(exit_status, Some(0) | None) {
            return 1;
        }
        if !scorecard.get("proof_artifacts_complete").and_then(Value::as_bool).unwrap_or(false) {
            return 1;
        }
    }
    0
}

fn scorecard_total(scorecard: &Value, key: &str) -> u64 {
    scorecard
        .get("totals")
        .and_then(Value::as_object)
        .and_then(|totals| totals.get(key))
        .and_then(Value::as_u64)
        .unwrap_or(0)
}

fn write_llm_directives(
    path: &Path,
    scorecard: &Value,
    test_exceptions: &TestExceptionLedger,
    validation_date: &str,
    patch_report: Option<&PatchApplicationReport>,
    fix_accounting: &Value,
    root: &Path,
) -> Result<(), PortError> {
    let failed_tests =
        scorecard.get("failed_tests").and_then(Value::as_array).cloned().unwrap_or_default();
    let tool_failures =
        scorecard.get("tool_failures").and_then(Value::as_array).cloned().unwrap_or_default();
    let validation_failures =
        scorecard.get("validation_failures").and_then(Value::as_array).cloned().unwrap_or_default();

    let mut output = String::new();
    pushln(&mut output, format_args!("# Upstream Rust Refresh Directives"));
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("Generated: {}", current_timestamp()));
    pushln(
        &mut output,
        format_args!(
            "Requested upstream revision: {}",
            string_field(scorecard, "requested_upstream_revision")
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "Resolved upstream revision: {}",
            string_field(scorecard, "resolved_upstream_revision")
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "Local repository revision: {}",
            string_field(scorecard, "local_repository_revision")
        ),
    );
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Canonical Command"));
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("```bash"));
    pushln(
        &mut output,
        format_args!(
            "targo trust domination upstream-tests --upstream-revision {} --out-dir {}",
            shell_quote(string_field(scorecard, "requested_upstream_revision")),
            shell_quote(
                scorecard
                    .get("artifacts")
                    .and_then(Value::as_object)
                    .and_then(|artifacts| artifacts.get("scorecard_md"))
                    .and_then(Value::as_str)
                    .and_then(|scorecard_path| scorecard_path.rsplit_once('/').map(|(dir, _)| dir))
                    .unwrap_or("reports/upstream-rust/porting/current")
            )
        ),
    );
    pushln(&mut output, format_args!("```"));
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Non-Negotiable Policy"));
    pushln(&mut output, format_args!(""));
    pushln(
        &mut output,
        format_args!(
            "- Keep the public path on Trust-owned binaries such as `targo` and `trustc`."
        ),
    );
    pushln(
        &mut output,
        format_args!("- Do not upload, publish, mirror, or release artifacts from this workflow."),
    );
    pushln(
        &mut output,
        format_args!(
            "- Do not turn a failing upstream test into success with a flag, environment variable, or undocumented fallback."
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "- Use `tests/upstream-rust/test-exceptions.toml` only for reviewed per-test failures, skips, or intentional divergences."
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "- Use `tests/upstream-rust/patches.toml` for deterministic upstream expectation patches that should reapply after every refetch."
        ),
    );
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Current Evidence"));
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("- failed tests: {}", scorecard_total(scorecard, "failed")));
    pushln(
        &mut output,
        format_args!("- tool failures: {}", scorecard_total(scorecard, "tool_failures")),
    );
    pushln(&mut output, format_args!("- validation failures: {}", validation_failures.len()));
    pushln(
        &mut output,
        format_args!(
            "- active test exceptions: {}",
            test_exceptions
                .exceptions
                .iter()
                .filter(|exception| exception.status == ExceptionStatus::Active)
                .count()
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "- active intentional divergences: {}",
            test_exceptions
                .exceptions
                .iter()
                .filter(|exception| {
                    exception.status == ExceptionStatus::Active
                        && exception.kind == TestExceptionKind::IntentionalDivergence
                })
                .count()
        ),
    );
    if let Some(report) = patch_report {
        pushln(
            &mut output,
            format_args!("- patch manifest: {}", display_path(&report.manifest_path, root)),
        );
        pushln(&mut output, format_args!("- active patches: {}", report.active_patch_ids.len()));
        pushln(&mut output, format_args!("- applied patches: {}", report.applied_patch_ids.len()));
    } else {
        pushln(&mut output, format_args!("- patch manifest: none"));
    }
    pushln(
        &mut output,
        format_args!(
            "- upstream fixes tracked: {}",
            fix_accounting
                .get("fixes_count")
                .map_or_else(|| "unknown".to_string(), value_to_markdown)
        ),
    );
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Declared Deviations"));
    pushln(&mut output, format_args!(""));
    let mut saw_divergence = false;
    for exception in &test_exceptions.exceptions {
        if exception.status == ExceptionStatus::Active
            && exception.kind == TestExceptionKind::IntentionalDivergence
        {
            saw_divergence = true;
            pushln(
                &mut output,
                format_args!(
                    "- {}: {} ({}) expires {}",
                    exception.id, exception.path, exception.reason, exception.expires_on
                ),
            );
        }
    }
    if !saw_divergence {
        pushln(&mut output, format_args!("- none"));
    }
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Failed Test Work Queue"));
    pushln(&mut output, format_args!(""));
    if failed_tests.is_empty() {
        pushln(&mut output, format_args!("- none"));
    } else {
        for failure in failed_tests.iter().take(50) {
            let suite = failure.get("suite").and_then(Value::as_str).unwrap_or("unknown");
            let test_path = failure.get("path").and_then(Value::as_str).unwrap_or("unknown");
            let category = failure.get("category").and_then(Value::as_str).unwrap_or("unknown");
            pushln(&mut output, format_args!("- [{suite}] {test_path} ({category})"));
        }
        if failed_tests.len() > 50 {
            pushln(
                &mut output,
                format_args!("- ... {} more failed tests omitted", failed_tests.len() - 50),
            );
        }
    }
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Tool Failure Work Queue"));
    pushln(&mut output, format_args!(""));
    if tool_failures.is_empty() {
        pushln(&mut output, format_args!("- none"));
    } else {
        for failure in &tool_failures {
            pushln(
                &mut output,
                format_args!(
                    "- {}: {}",
                    failure.get("kind").and_then(Value::as_str).unwrap_or("tool"),
                    failure.get("message").and_then(Value::as_str).unwrap_or("no message")
                ),
            );
        }
    }
    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Patch and Ledger Update Rules"));
    pushln(&mut output, format_args!(""));
    pushln(
        &mut output,
        format_args!(
            "1. Fix compiler/tool behavior when the upstream test exposes a real Trust regression."
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "2. Add or update `tests/upstream-rust/patches.toml` only for deterministic expectation text drift that should reapply after refetch."
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "3. Add a `test-exceptions.toml` row only when the result is an intentional Trust divergence or a temporary tracked failure with owner, issue, expiry, and bounded patterns."
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "4. Rerun the canonical command until failed tests, tool failures, validation failures, stale paths, and unclassified upstream-fix actions are zero or ledgered."
        ),
    );
    pushln(&mut output, format_args!(""));
    pushln(
        &mut output,
        format_args!("Validation date for exception and patch expiry checks: {validation_date}"),
    );

    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_scorecard_markdown(path: &Path, scorecard: &Value) -> Result<(), PortError> {
    let mut output = String::new();
    let totals = scorecard.get("totals").and_then(Value::as_object);
    let failed_tests =
        scorecard.get("failed_tests").and_then(Value::as_array).cloned().unwrap_or_default();
    let tool_failures =
        scorecard.get("tool_failures").and_then(Value::as_array).cloned().unwrap_or_default();

    pushln(&mut output, format_args!("# Upstream Rust Porting Scorecard"));
    pushln(&mut output, format_args!(""));
    pushln(
        &mut output,
        format_args!(
            "Requested upstream revision: {}",
            string_field(scorecard, "requested_upstream_revision")
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "Requested upstream ref: {}",
            string_field(scorecard, "requested_upstream_ref")
        ),
    );
    pushln(
        &mut output,
        format_args!("Upstream remote: {}", string_field(scorecard, "upstream_remote")),
    );
    let resolution = scorecard.get("upstream_resolution").and_then(Value::as_object);
    pushln(
        &mut output,
        format_args!(
            "Resolution source: {}",
            resolution
                .and_then(|value| value.get("source"))
                .and_then(Value::as_str)
                .unwrap_or("unknown")
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "Resolution detail: {}",
            resolution
                .and_then(|value| value.get("source_detail"))
                .and_then(Value::as_str)
                .unwrap_or("unknown")
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "Local repository revision: {}",
            string_field(scorecard, "local_repository_revision")
        ),
    );
    pushln(
        &mut output,
        format_args!("Baseline revision: {}", string_field(scorecard, "baseline_revision")),
    );
    pushln(
        &mut output,
        format_args!(
            "Resolved upstream revision: {}",
            string_field(scorecard, "resolved_upstream_revision")
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "Failed tests: {}",
            totals.and_then(|value| value.get("failed")).and_then(Value::as_u64).unwrap_or(0)
        ),
    );
    pushln(
        &mut output,
        format_args!(
            "Tool build failures: {}",
            totals
                .and_then(|value| value.get("tool_failures"))
                .and_then(Value::as_u64)
                .unwrap_or(0)
        ),
    );

    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Revision Drift"));
    pushln(&mut output, format_args!(""));
    if let Some(drift) = scorecard.get("upstream_revision_drift").and_then(Value::as_object) {
        for key in [
            "requested_revision",
            "requested_ref",
            "upstream_remote",
            "resolved_revision",
            "drifted_from_baseline",
            "requires_upstream_fix_review",
        ] {
            let label = key.replace('_', " ");
            let value = drift.get(key).map_or_else(|| "unknown".to_string(), value_to_markdown);
            pushln(&mut output, format_args!("- {label}: {value}"));
        }
    } else {
        pushln(&mut output, format_args!("- unknown"));
    }

    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Upstream Fix Accounting"));
    pushln(&mut output, format_args!(""));
    if let Some(accounting) = scorecard.get("upstream_fix_accounting").and_then(Value::as_object) {
        pushln(
            &mut output,
            format_args!(
                "- ledger: {}",
                accounting
                    .get("ledger_path")
                    .map_or_else(|| "unknown".to_string(), value_to_markdown)
            ),
        );
        pushln(
            &mut output,
            format_args!(
                "- fixes tracked: {}",
                accounting
                    .get("fixes_count")
                    .map_or_else(|| "unknown".to_string(), value_to_markdown)
            ),
        );
        push_counts(&mut output, "- fix statuses", accounting.get("status_counts"));
        push_counts(&mut output, "- local actions", accounting.get("local_action_counts"));
        pushln(
            &mut output,
            format_args!(
                "- pending local actions: {}",
                accounting
                    .get("pending_local_actions_count")
                    .map_or_else(|| "0".to_string(), value_to_markdown)
            ),
        );
        pushln(
            &mut output,
            format_args!(
                "- reviewed through current revision: {}",
                accounting
                    .get("reviewed_through_current_revision")
                    .map_or_else(|| "unknown".to_string(), value_to_markdown)
            ),
        );
        pushln(
            &mut output,
            format_args!(
                "- claim: {}",
                accounting
                    .get("applicable_fix_tracking_claim")
                    .and_then(Value::as_str)
                    .unwrap_or("unknown")
            ),
        );
        if let Some(actions) = accounting.get("pending_local_actions").and_then(Value::as_array)
            && !actions.is_empty()
        {
            pushln(&mut output, format_args!(""));
            for action in actions {
                let id = action.get("id").and_then(Value::as_str).unwrap_or("unknown");
                let local_action =
                    action.get("local_action").and_then(Value::as_str).unwrap_or("unknown");
                let title = action.get("title").and_then(Value::as_str).unwrap_or("unknown");
                pushln(&mut output, format_args!("- {id} [{local_action}]: {title}"));
            }
        }
    } else {
        pushln(&mut output, format_args!("- unknown"));
    }

    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Patch And Deviation Accounting"));
    pushln(&mut output, format_args!(""));
    if let Some(patches) = scorecard.get("patch_manifest_accounting").and_then(Value::as_object) {
        pushln(
            &mut output,
            format_args!(
                "- patch manifest: {}",
                patches.get("path").map_or_else(|| "unknown".to_string(), value_to_markdown)
            ),
        );
        pushln(
            &mut output,
            format_args!(
                "- active patches: {}",
                patches
                    .get("active_patch_count")
                    .map_or_else(|| "0".to_string(), value_to_markdown)
            ),
        );
        pushln(
            &mut output,
            format_args!(
                "- applied patches: {}",
                patches
                    .get("applied_patch_count")
                    .map_or_else(|| "0".to_string(), value_to_markdown)
            ),
        );
    } else {
        pushln(&mut output, format_args!("- patch manifest: unknown"));
    }
    if let Some(exceptions) = scorecard.get("test_exception_accounting").and_then(Value::as_object)
    {
        pushln(
            &mut output,
            format_args!(
                "- active test exceptions: {}",
                exceptions
                    .get("active_exception_count")
                    .map_or_else(|| "0".to_string(), value_to_markdown)
            ),
        );
        pushln(
            &mut output,
            format_args!(
                "- active intentional divergences: {}",
                exceptions
                    .get("active_intentional_divergence_count")
                    .map_or_else(|| "0".to_string(), value_to_markdown)
            ),
        );
    }
    pushln(
        &mut output,
        format_args!("- llm directives: {}", stringish_field(scorecard, "llm_directives_path")),
    );

    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Validation Failures"));
    pushln(&mut output, format_args!(""));
    let validation_failures =
        scorecard.get("validation_failures").and_then(Value::as_array).cloned().unwrap_or_default();
    if validation_failures.is_empty() {
        pushln(&mut output, format_args!("- none"));
    } else {
        for failure in validation_failures {
            let kind = failure.get("kind").and_then(Value::as_str).unwrap_or("validation-failure");
            let message = failure.get("message").and_then(Value::as_str).unwrap_or("no message");
            pushln(&mut output, format_args!("- {kind}: {message}"));
        }
    }

    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Categories"));
    pushln(&mut output, format_args!(""));
    if let Some(categories) =
        totals.and_then(|value| value.get("categories")).and_then(Value::as_object)
    {
        if categories.is_empty() {
            pushln(&mut output, format_args!("- none"));
        } else {
            for (category, count) in categories {
                pushln(&mut output, format_args!("- {category}: {}", value_to_markdown(count)));
            }
        }
    } else {
        pushln(&mut output, format_args!("- none"));
    }

    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Failed Tests"));
    pushln(&mut output, format_args!(""));
    if failed_tests.is_empty() {
        pushln(&mut output, format_args!("- none"));
    } else {
        for failure in failed_tests {
            let suite = failure.get("suite").and_then(Value::as_str).unwrap_or("unknown");
            let test_path = failure.get("path").and_then(Value::as_str).unwrap_or("unknown");
            let category = failure.get("category").and_then(Value::as_str).unwrap_or("unknown");
            pushln(&mut output, format_args!("- [{suite}] {test_path} ({category})"));
            if let Some(artifacts) = failure.get("actual_artifacts").and_then(Value::as_array)
                && !artifacts.is_empty()
            {
                let text = artifacts
                    .iter()
                    .filter_map(|artifact| {
                        Some(format!(
                            "{}:{}",
                            artifact.get("kind")?.as_str()?,
                            artifact.get("path")?.as_str()?
                        ))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                if !text.is_empty() {
                    pushln(&mut output, format_args!("  - actual artifacts: {text}"));
                }
            }
            if let Some(comparison) =
                failure.get("comparisons").and_then(Value::as_array).and_then(|items| items.first())
            {
                pushln(
                    &mut output,
                    format_args!(
                        "  - expected-vs-actual: {} -> {} at log line {}",
                        comparison
                            .get("expected")
                            .map_or_else(|| "unknown".to_string(), value_to_markdown),
                        comparison
                            .get("actual")
                            .map_or_else(|| "unknown".to_string(), value_to_markdown),
                        comparison
                            .get("line")
                            .map_or_else(|| "unknown".to_string(), value_to_markdown)
                    ),
                );
            }
            if let Some(snippet) = failure.get("failure_snippet").and_then(Value::as_object) {
                pushln(
                    &mut output,
                    format_args!(
                        "  - snippet: log lines {}-{}",
                        snippet
                            .get("start_line")
                            .map_or_else(|| "unknown".to_string(), value_to_markdown),
                        snippet
                            .get("end_line")
                            .map_or_else(|| "unknown".to_string(), value_to_markdown)
                    ),
                );
            }
        }
    }

    pushln(&mut output, format_args!(""));
    pushln(&mut output, format_args!("## Tool Failures"));
    pushln(&mut output, format_args!(""));
    if tool_failures.is_empty() {
        pushln(&mut output, format_args!("- none"));
    } else {
        for failure in tool_failures {
            pushln(
                &mut output,
                format_args!(
                    "- {}: {}: {}",
                    failure.get("kind").and_then(Value::as_str).unwrap_or("tool"),
                    failure.get("crate").and_then(Value::as_str).unwrap_or("unknown"),
                    failure.get("message").and_then(Value::as_str).unwrap_or("")
                ),
            );
        }
    }

    if scorecard.get("proof_artifacts_complete").is_some() {
        pushln(&mut output, format_args!(""));
        pushln(&mut output, format_args!("## Proof Accounting"));
        pushln(&mut output, format_args!(""));
        for key in [
            "proof_mode",
            "proof_required_for_exit",
            "proof_accounting_status",
            "proof_artifacts_complete",
        ] {
            pushln(
                &mut output,
                format_args!("- {}: {}", key.replace('_', " "), stringish_field(scorecard, key)),
            );
        }
        if let Some(validation) = scorecard
            .get("proof_artifact_validation")
            .and_then(Value::as_object)
            .and_then(|value| value.get("summary_totals"))
            .and_then(Value::as_object)
        {
            pushln(
                &mut output,
                format_args!(
                    "- proof totals: total={} passed={} excepted={} unaccounted={}",
                    validation
                        .get("total")
                        .map_or_else(|| "unknown".to_string(), value_to_markdown),
                    validation
                        .get("passed")
                        .map_or_else(|| "unknown".to_string(), value_to_markdown),
                    validation
                        .get("excepted")
                        .map_or_else(|| "unknown".to_string(), value_to_markdown),
                    validation
                        .get("unaccounted")
                        .map_or_else(|| "unknown".to_string(), value_to_markdown)
                ),
            );
        }
    }

    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn push_counts(output: &mut String, label: &str, value: Option<&Value>) {
    let Some(map) = value.and_then(Value::as_object) else {
        return;
    };
    if map.is_empty() {
        return;
    }
    let counts = map
        .iter()
        .map(|(key, value)| format!("{key}={}", value_to_markdown(value)))
        .collect::<Vec<_>>()
        .join(", ");
    pushln(output, format_args!("{label}: {counts}"));
}

fn string_field<'a>(scorecard: &'a Value, key: &str) -> &'a str {
    scorecard.get(key).and_then(Value::as_str).unwrap_or("unknown")
}

fn stringish_field(scorecard: &Value, key: &str) -> String {
    scorecard.get(key).map_or_else(|| "unknown".to_string(), value_to_markdown)
}

fn value_to_markdown(value: &Value) -> String {
    match value {
        Value::Null => "unknown".to_string(),
        Value::Bool(value) => value.to_string(),
        Value::Number(value) => value.to_string(),
        Value::String(value) => value.clone(),
        other => other.to_string(),
    }
}

fn proof_required_for_exit(execute: bool, proof_mode: ProofMode) -> bool {
    execute && proof_mode == ProofMode::Full
}

fn proof_accounting_status(
    execute: bool,
    proof_mode: ProofMode,
    proof_artifacts_complete: bool,
    execution_exit_status: Option<i32>,
) -> &'static str {
    if proof_artifacts_complete {
        "complete"
    } else if !execute {
        "not_run"
    } else if proof_mode == ProofMode::Full {
        "full_proof_incomplete"
    } else if !matches!(execution_exit_status, Some(0) | None) {
        "smoke_proof_incomplete_nonblocking"
    } else {
        "smoke_proof_incomplete"
    }
}

fn proof_artifact_validation(
    proof_dir: &Path,
    release: bool,
    test_exceptions: &TestExceptionLedger,
    validation_date: &str,
    bounded_inventory: bool,
) -> Result<Value, PortError> {
    let mut artifacts = serde_json::Map::new();
    let mut missing = Vec::<String>::new();
    let mut invalid = BTreeSet::<String>::new();
    let mut loaded = BTreeMap::<String, Value>::new();

    for name in PROOF_ARTIFACT_NAMES {
        let path = proof_dir.join(name);
        let mut record = serde_json::Map::new();
        record.insert("path".to_string(), json!(path.to_string_lossy()));
        record.insert("exists".to_string(), json!(path.exists()));
        record.insert("valid".to_string(), json!(false));
        if !path.exists() {
            missing.push(name.to_string());
            artifacts.insert(name.to_string(), Value::Object(record));
            continue;
        }
        let data = fs::read(&path)?;
        record.insert("size_bytes".to_string(), json!(data.len()));
        record.insert("sha256".to_string(), json!(sha256_bytes(&data)));
        if data.is_empty() {
            record.insert("error".to_string(), json!("proof artifact is empty"));
            invalid.insert(name.to_string());
            artifacts.insert(name.to_string(), Value::Object(record));
            continue;
        }
        match serde_json::from_slice::<Value>(&data) {
            Ok(Value::Object(_)) => {
                record.insert("valid".to_string(), json!(true));
                loaded.insert(name.to_string(), serde_json::from_slice::<Value>(&data)?);
            }
            Ok(_) => {
                record.insert(
                    "error".to_string(),
                    json!("proof artifact top-level JSON value must be an object"),
                );
                invalid.insert(name.to_string());
            }
            Err(error) => {
                record.insert(
                    "error".to_string(),
                    json!(format!("proof artifact is not valid UTF-8 JSON: {error}")),
                );
                invalid.insert(name.to_string());
            }
        }
        artifacts.insert(name.to_string(), Value::Object(record));
    }

    let typed_inventory = loaded.get("inventory.json").and_then(|artifact| {
        match serde_json::to_string(artifact)
            .map_err(ParseError::from)
            .and_then(|input| parse_test_inventory_json(&input))
        {
            Ok(inventory) => Some(inventory),
            Err(error) => {
                mark_invalid(
                    &mut artifacts,
                    &mut invalid,
                    "inventory.json",
                    &format!("inventory does not match typed proof schema: {error}"),
                );
                None
            }
        }
    });
    let typed_results =
        loaded.get("results.json").and_then(|artifact| {
            match serde_json::to_string(artifact)
                .map_err(ParseError::from)
                .and_then(|input| parse_test_result_report_json(&input))
            {
                Ok(results) => Some(results),
                Err(error) => {
                    mark_invalid(
                        &mut artifacts,
                        &mut invalid,
                        "results.json",
                        &format!("results do not match typed proof schema: {error}"),
                    );
                    None
                }
            }
        });
    let typed_summary = loaded.get("proof-summary.json").and_then(|artifact| {
        match serde_json::from_value::<TestProofTotals>(artifact.clone()) {
            Ok(summary) => Some(summary),
            Err(error) => {
                mark_invalid(
                    &mut artifacts,
                    &mut invalid,
                    "proof-summary.json",
                    &format!("summary does not match typed proof totals schema: {error}"),
                );
                None
            }
        }
    });
    if let Some(inventory) = &typed_inventory {
        validate_typed_trust_added_paths(inventory, &mut artifacts, &mut invalid);
    }
    let trust_added_manifest =
        read_proof_trust_added_manifest(proof_dir, &mut artifacts, &mut invalid)?;
    if let (Some(inventory), Some(results), Some(summary)) =
        (&typed_inventory, &typed_results, &typed_summary)
    {
        let filtered_exceptions;
        let validation_exceptions = if bounded_inventory {
            filtered_exceptions = test_exceptions_for_inventory(test_exceptions, inventory);
            &filtered_exceptions
        } else {
            test_exceptions
        };
        match validate_test_proof_bundle(TestProofBundle {
            inventory,
            results,
            exceptions: validation_exceptions,
            trust_added_tests: trust_added_manifest.as_ref(),
            validation_date,
            release,
        }) {
            Ok(computed) if computed == *summary => {}
            Ok(computed) => {
                mark_invalid(
                    &mut artifacts,
                    &mut invalid,
                    "proof-summary.json",
                    &format!(
                        "summary totals do not match typed proof bundle: expected {:?}, got {:?}",
                        computed, summary
                    ),
                );
            }
            Err(findings) => {
                let findings_json = findings
                    .iter()
                    .map(|finding| {
                        json!({
                            "field": finding.field,
                            "message": finding.message,
                        })
                    })
                    .collect::<Vec<_>>();
                for artifact_name in ["inventory.json", "results.json", "proof-summary.json"] {
                    mark_invalid(
                        &mut artifacts,
                        &mut invalid,
                        artifact_name,
                        "typed proof bundle validation failed",
                    );
                }
                if let Some(record) =
                    artifacts.get_mut("proof-summary.json").and_then(Value::as_object_mut)
                {
                    record.insert("validation_findings".to_string(), json!(findings_json));
                }
            }
        }
    }

    let inventory_ids = collect_json_ids(
        loaded.get("inventory.json"),
        "tests",
        "id",
        "inventory.json",
        &mut invalid,
        &mut artifacts,
    );
    let result_ids = collect_json_ids(
        loaded.get("results.json"),
        "results",
        "test_id",
        "results.json",
        &mut invalid,
        &mut artifacts,
    );
    let mut summary_totals = BTreeMap::<String, u64>::new();
    if let Some(summary) = loaded.get("proof-summary.json").and_then(Value::as_object) {
        for key in [
            "total",
            "upstream",
            "trust_added",
            "passed",
            "upstream_inapplicable",
            "excepted",
            "unaccounted",
        ] {
            if let Some(value) = summary.get(key).and_then(Value::as_u64) {
                summary_totals.insert(key.to_string(), value);
            } else {
                mark_invalid(
                    &mut artifacts,
                    &mut invalid,
                    "proof-summary.json",
                    &format!("{key} must be a non-negative integer"),
                );
            }
        }
        if let Some(total) = summary_totals.get("total").copied() {
            if total == 0 {
                mark_invalid(
                    &mut artifacts,
                    &mut invalid,
                    "proof-summary.json",
                    "proof total must be positive",
                );
            }
            if summary_totals.get("upstream").copied().unwrap_or(0)
                + summary_totals.get("trust_added").copied().unwrap_or(0)
                != total
            {
                mark_invalid(
                    &mut artifacts,
                    &mut invalid,
                    "proof-summary.json",
                    "upstream + trust_added must equal total",
                );
            }
            let accounted = summary_totals.get("passed").copied().unwrap_or(0)
                + summary_totals.get("upstream_inapplicable").copied().unwrap_or(0)
                + summary_totals.get("excepted").copied().unwrap_or(0)
                + summary_totals.get("unaccounted").copied().unwrap_or(0);
            if accounted != total {
                mark_invalid(
                    &mut artifacts,
                    &mut invalid,
                    "proof-summary.json",
                    "passed + upstream_inapplicable + excepted + unaccounted must equal total",
                );
            }
            if inventory_ids.len() as u64 != total {
                mark_invalid(
                    &mut artifacts,
                    &mut invalid,
                    "proof-summary.json",
                    "summary total does not match inventory test count",
                );
            }
            if result_ids.len() as u64 != total {
                mark_invalid(
                    &mut artifacts,
                    &mut invalid,
                    "proof-summary.json",
                    "summary total does not match result count",
                );
            }
        }
        if summary_totals.get("unaccounted").copied().unwrap_or(0) != 0 {
            mark_invalid(
                &mut artifacts,
                &mut invalid,
                "proof-summary.json",
                "unaccounted proof total must be zero",
            );
        }
    }

    let inventory_set = inventory_ids.into_iter().collect::<BTreeSet<_>>();
    let result_set = result_ids.into_iter().collect::<BTreeSet<_>>();
    let missing_results = inventory_set.difference(&result_set).cloned().collect::<Vec<_>>();
    let extra_results = result_set.difference(&inventory_set).cloned().collect::<Vec<_>>();
    if !missing_results.is_empty() {
        mark_invalid(
            &mut artifacts,
            &mut invalid,
            "results.json",
            &format!(
                "results are missing inventory ids: {}",
                missing_results.into_iter().take(10).collect::<Vec<_>>().join(", ")
            ),
        );
    }
    if !extra_results.is_empty() {
        mark_invalid(
            &mut artifacts,
            &mut invalid,
            "results.json",
            &format!(
                "results include ids not present in inventory: {}",
                extra_results.into_iter().take(10).collect::<Vec<_>>().join(", ")
            ),
        );
    }

    Ok(json!({
        "complete": missing.is_empty() && invalid.is_empty(),
        "missing": missing,
        "invalid": invalid.into_iter().collect::<Vec<_>>(),
        "artifacts": artifacts,
        "summary_totals": summary_totals,
    }))
}

fn test_exceptions_for_inventory(
    test_exceptions: &TestExceptionLedger,
    inventory: &TestInventory,
) -> TestExceptionLedger {
    let inventory_ids =
        inventory.tests.iter().map(|test| test.id.as_str()).collect::<BTreeSet<_>>();
    TestExceptionLedger {
        schema_version: test_exceptions.schema_version.clone(),
        exceptions: test_exceptions
            .exceptions
            .iter()
            .filter(|exception| inventory_ids.contains(exception.test_id.as_str()))
            .cloned()
            .collect(),
    }
}

fn read_proof_trust_added_manifest(
    proof_dir: &Path,
    artifacts: &mut serde_json::Map<String, Value>,
    invalid: &mut BTreeSet<String>,
) -> Result<Option<TrustAddedTestManifest>, PortError> {
    let candidates = ["trust-added-manifest.json", "trust-added-manifest.toml"];
    for name in candidates {
        let path = proof_dir.join(name);
        if !path.exists() {
            continue;
        }
        let data = fs::read_to_string(&path)?;
        let mut record = serde_json::Map::new();
        record.insert("path".to_string(), json!(path.to_string_lossy()));
        record.insert("exists".to_string(), json!(true));
        record.insert("size_bytes".to_string(), json!(data.len()));
        record.insert("sha256".to_string(), json!(sha256_bytes(data.as_bytes())));
        let parsed = match document_format(&path) {
            DocumentFormat::Json => parse_trust_added_tests_json(&data),
            DocumentFormat::Toml => parse_trust_added_tests_toml(&data),
        };
        match parsed {
            Ok(manifest) => {
                record.insert("valid".to_string(), json!(true));
                artifacts.insert(name.to_string(), Value::Object(record));
                return Ok(Some(manifest));
            }
            Err(error) => {
                record.insert("valid".to_string(), json!(false));
                record.insert(
                    "error".to_string(),
                    json!(format!("Trust-added manifest does not match typed schema: {error}")),
                );
                artifacts.insert(name.to_string(), Value::Object(record));
                invalid.insert(name.to_string());
                return Ok(None);
            }
        }
    }
    Ok(None)
}

fn validate_typed_trust_added_paths(
    inventory: &TestInventory,
    artifacts: &mut serde_json::Map<String, Value>,
    invalid: &mut BTreeSet<String>,
) {
    for test in &inventory.tests {
        if test.source == TestSource::TrustAdded && !test.path.starts_with("tests/trust-added/") {
            mark_invalid(
                artifacts,
                invalid,
                "inventory.json",
                &format!(
                    "Trust-added inventory test '{}' must use a repository-relative tests/trust-added/ manifest path, not '{}'",
                    test.id, test.path
                ),
            );
        }
    }
}

fn append_porting_validation_failures(
    mut failures: Vec<Value>,
    execute: bool,
    max_files: Option<usize>,
    missing_locally: &[String],
) -> Vec<Value> {
    if execute && max_files.is_none() && !missing_locally.is_empty() {
        failures.push(json!({
            "kind": "ported-overlay-not-applied",
            "message": format!(
                "full execution cannot prove latest upstream coverage while {} upstream test paths are missing from tests/; run with --apply or port the missing tests",
                missing_locally.len()
            ),
            "sample": missing_locally.iter().take(20).collect::<Vec<_>>(),
        }));
    }
    failures
}

fn collect_json_ids(
    artifact: Option<&Value>,
    array_key: &str,
    id_key: &str,
    artifact_name: &str,
    invalid: &mut BTreeSet<String>,
    artifacts: &mut serde_json::Map<String, Value>,
) -> Vec<String> {
    let mut ids = Vec::new();
    let Some(rows) = artifact
        .and_then(Value::as_object)
        .and_then(|object| object.get(array_key))
        .and_then(Value::as_array)
    else {
        if artifact.is_some() {
            mark_invalid(artifacts, invalid, artifact_name, &format!("{array_key} must be a list"));
        }
        return ids;
    };
    let mut seen = BTreeSet::new();
    for (index, row) in rows.iter().enumerate() {
        let Some(test_id) =
            row.as_object().and_then(|object| object.get(id_key)).and_then(Value::as_str)
        else {
            mark_invalid(
                artifacts,
                invalid,
                artifact_name,
                &format!("{array_key}[{index}].{id_key} must be a non-empty string"),
            );
            continue;
        };
        if test_id.trim().is_empty() {
            mark_invalid(
                artifacts,
                invalid,
                artifact_name,
                &format!("{array_key}[{index}].{id_key} must be a non-empty string"),
            );
            continue;
        }
        if !seen.insert(test_id.to_string()) {
            mark_invalid(
                artifacts,
                invalid,
                artifact_name,
                &format!("duplicate {id_key}: {test_id}"),
            );
        }
        ids.push(test_id.to_string());
    }
    if let Some(record) = artifacts.get_mut(artifact_name).and_then(Value::as_object_mut) {
        record.insert(
            if id_key == "id" { "test_count" } else { "result_count" }.to_string(),
            json!(ids.len()),
        );
    }
    ids
}

fn mark_invalid(
    artifacts: &mut serde_json::Map<String, Value>,
    invalid: &mut BTreeSet<String>,
    name: &str,
    message: &str,
) {
    invalid.insert(name.to_string());
    if let Some(record) = artifacts.get_mut(name).and_then(Value::as_object_mut) {
        record.insert("valid".to_string(), json!(false));
        record.insert("error".to_string(), json!(message));
    }
}

struct SuiteExecution {
    exit_status: i32,
    execution_log: PathBuf,
    scorecard_log: PathBuf,
    cargo_driver: Vec<String>,
    telemetry: Value,
}

#[derive(Debug, Clone)]
struct TrustAddedCommandExecution {
    command: TrustAddedTestCommand,
    exit_status: i32,
}

#[derive(Debug, Clone)]
struct TrustAddedExecution {
    manifest_path: PathBuf,
    manifest: TrustAddedTestManifest,
    log_path: PathBuf,
    commands: Vec<TrustAddedCommandExecution>,
}

#[derive(Debug, Default)]
struct TrustAddedProofOutcome {
    command_ids: Vec<String>,
    command_lines: Vec<String>,
    failed: bool,
}

#[derive(Debug, Clone)]
struct ProofUpstreamTest {
    id: String,
    path: String,
    source_git_blob: Option<String>,
}

#[allow(clippy::too_many_arguments)] // suite runner ties together every dimension of one test invocation
fn execute_suite(
    root: &Path,
    out_dir: &Path,
    resolved_revision: &str,
    extra_args: &str,
    target_triple: Option<&str>,
    host_triple: Option<&str>,
    release: bool,
    max_files: Option<usize>,
    upstream_entries: &[GitTreeEntry],
    exported_paths: &[String],
    local_head: &str,
    test_exceptions: &TestExceptionLedger,
    test_exception_validation_date: &str,
) -> Result<SuiteExecution, PortError> {
    let log_path = out_dir.join("execution.log");
    let proof_dir = out_dir.join("proof");
    let proof_log_path = proof_dir.join("upstream-rust-compat.log");
    let release_driver = if release { Some(resolve_trust_cargo(root, true)?) } else { None };
    let proof_tests = proof_inventory_tests(max_files, upstream_entries, exported_paths);
    let trust_added_manifest =
        if max_files.is_none() { Some(read_trust_added_manifest(root)?) } else { None };
    let trust_added_test_count = trust_added_manifest
        .as_ref()
        .map(|(_, manifest)| trust_added_inventory_ids(manifest).len())
        .unwrap_or(0);
    let mut command = rust_bootstrap_command(root)?;
    let command_paths = if max_files.is_some() {
        proof_tests.iter().map(|test| test.path.clone()).collect()
    } else {
        Vec::new()
    };
    command.extend([
        "test".to_string(),
        "--src".to_string(),
        root.to_string_lossy().into_owned(),
        "--stage".to_string(),
        "2".to_string(),
        "--trust-vanilla".to_string(),
        "--no-fail-fast".to_string(),
    ]);
    let config = root.join("config.toml");
    if config.is_file() {
        command.extend(["--config".to_string(), config.to_string_lossy().into_owned()]);
    }
    if let Some(host_triple) = non_empty_option(host_triple) {
        command.extend(["--host".to_string(), host_triple.to_string()]);
    }
    if let Some(target_triple) = non_empty_option(target_triple) {
        command.extend(["--target".to_string(), target_triple.to_string()]);
    }
    command.extend(command_paths);
    command.extend(split_words(extra_args));
    let execution_command = shell_join(&command);

    if let Some(parent) = log_path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::create_dir_all(&proof_dir)?;
    let started_at = current_timestamp();
    let started = Instant::now();
    let mut log = OpenOptions::new().create(true).write(true).truncate(true).open(&log_path)?;
    writeln!(log, "$ {execution_command}")?;
    writeln!(log, "# executor=rust-bootstrap")?;
    writeln!(log, "# resolved_upstream_revision={resolved_revision}")?;
    writeln!(log, "# proof_inventory_tests={}", proof_tests.len() + trust_added_test_count)?;
    writeln!(log, "# upstream_proof_inventory_tests={}", proof_tests.len())?;
    writeln!(log, "# trust_added_proof_inventory_tests={trust_added_test_count}")?;
    writeln!(log, "# started_at={started_at}")?;
    log.flush()?;
    let stdout = log.try_clone()?;
    let stderr = log.try_clone()?;
    let mut process = Command::new(&command[0]);
    process.args(&command[1..]).current_dir(root);
    process.stdout(Stdio::from(stdout)).stderr(Stdio::from(stderr));
    process.env("TRUST_UPSTREAM_RUST_EXECUTOR", "rust-bootstrap");
    process.env("TRUST_UPSTREAM_RUST_CURRENT_REVISION", resolved_revision);
    process.env("TRUST_STRICT", "1");
    process.env("TRUST_RELEASE_GATE", if release { "1" } else { "0" });
    process.env("TRUST_UPSTREAM_RUST_PROOF_DIR", &proof_dir);
    // The bootstrap driver establishes its own narrowly scoped rustc/rustdoc
    // shim policy. This evidence runner must not manufacture Targo frontend
    // authority or propagate a caller's retired marker into the child.
    for marker in [
        "TRUST_BOOTSTRAP_NO_VERIFY",
        "TRUST_BOOTSTRAP_NO_VERIFY_TARGET_ONLY",
        "TRUST_BOOTSTRAP_SHIM_NO_VERIFY",
        "TRUST_BOOTSTRAP_SHIM_NO_VERIFY_TARGET_ONLY",
    ] {
        process.env_remove(marker);
    }
    let status = process.status()?;
    let upstream_exit_status = status.code().unwrap_or(-1);
    let trust_added = match trust_added_manifest {
        Some((manifest_path, manifest)) => {
            execute_trust_added_manifest(root, &proof_dir, manifest_path, manifest, release)?
        }
        None => empty_trust_added_execution(&proof_dir),
    };
    let execution_exit_status = combined_execution_exit_status(upstream_exit_status, &trust_added);
    let ended_at = current_timestamp();
    let duration_seconds = started.elapsed().as_secs_f64();
    writeln!(log, "# ended_at={ended_at}")?;
    writeln!(log, "# duration_seconds={duration_seconds:.3}")?;
    writeln!(log, "# upstream_exit_status={upstream_exit_status}")?;
    writeln!(log, "# trust_added_exit_status={}", trust_added_exit_status(&trust_added))?;
    writeln!(log, "# exit_status={execution_exit_status}")?;
    log.flush()?;
    fs::copy(&log_path, &proof_log_path)?;
    write_execution_proof_artifacts(
        root,
        &proof_dir,
        resolved_revision,
        local_head,
        &proof_tests,
        upstream_exit_status,
        &trust_added,
        &log_path,
        &execution_command,
        release,
        test_exceptions,
        test_exception_validation_date,
    )?;
    let scorecard_log = proof_log_path;
    Ok(SuiteExecution {
        exit_status: execution_exit_status,
        execution_log: log_path,
        scorecard_log,
        cargo_driver: release_driver.unwrap_or_else(|| command.clone()),
        telemetry: json!({
            "started_at": started_at,
            "ended_at": ended_at,
            "duration_seconds": (duration_seconds * 1000.0).round() / 1000.0,
            "exit_status": execution_exit_status,
            "upstream_exit_status": upstream_exit_status,
            "trust_added_exit_status": trust_added_exit_status(&trust_added),
            "executor": "rust-bootstrap",
            "proof_inventory_tests": proof_tests.len() + trust_added_test_count,
            "upstream_proof_inventory_tests": proof_tests.len(),
            "trust_added_proof_inventory_tests": trust_added_test_count,
            "trust_added_manifest_executed": max_files.is_none(),
            "trust_added_manifest": display_path(&trust_added.manifest_path, root),
            "trust_added_commands": trust_added.commands.iter().map(|command| {
                json!({
                    "id": &command.command.id,
                    "exit_status": command.exit_status,
                })
            }).collect::<Vec<_>>(),
        }),
    })
}

fn non_empty_option(value: Option<&str>) -> Option<&str> {
    value.map(str::trim).filter(|value| !value.is_empty())
}

fn empty_trust_added_execution(proof_dir: &Path) -> TrustAddedExecution {
    TrustAddedExecution {
        manifest_path: PathBuf::from(TRUST_ADDED_MANIFEST),
        manifest: TrustAddedTestManifest {
            schema_version: crate::SCHEMA_VERSION.to_string(),
            commands: Vec::new(),
        },
        log_path: proof_dir.join("trust-added.log"),
        commands: Vec::new(),
    }
}

fn read_trust_added_manifest(root: &Path) -> Result<(PathBuf, TrustAddedTestManifest), PortError> {
    let path = match env::var(TRUST_ADDED_MANIFEST_ENV) {
        Ok(configured) if configured.trim().is_empty() => {
            return Err(PortError::Message(format!("{TRUST_ADDED_MANIFEST_ENV} is empty")));
        }
        Ok(configured) => root_path(root, Path::new(&configured)),
        Err(_) => root.join(TRUST_ADDED_MANIFEST),
    };
    let input = fs::read_to_string(&path).map_err(|error| {
        PortError::Message(format!(
            "failed to read Trust-added proof manifest {}: {error}",
            display_path(&path, root)
        ))
    })?;
    let manifest = match document_format(&path) {
        DocumentFormat::Json => parse_trust_added_tests_json(&input),
        DocumentFormat::Toml => parse_trust_added_tests_toml(&input),
    }
    .map_err(|source| {
        PortError::Message(format!(
            "failed to parse Trust-added proof manifest {}: {source}",
            display_path(&path, root)
        ))
    })?;
    validate_trust_added_tests(&manifest).map_err(|findings| {
        PortError::Message(format!(
            "Trust-added proof manifest {} failed validation:\n{}",
            display_path(&path, root),
            format_validation_findings(&findings)
        ))
    })?;
    reject_trust_added_script_launchers(root, &manifest)?;
    Ok((path, manifest))
}

fn execute_trust_added_manifest(
    root: &Path,
    proof_dir: &Path,
    manifest_path: PathBuf,
    manifest: TrustAddedTestManifest,
    release: bool,
) -> Result<TrustAddedExecution, PortError> {
    fs::create_dir_all(proof_dir)?;
    let log_path = proof_dir.join("trust-added.log");
    write_json(&proof_dir.join("trust-added-manifest.json"), &serde_json::to_value(&manifest)?)?;
    let mut log = OpenOptions::new().create(true).write(true).truncate(true).open(&log_path)?;
    writeln!(log, "# manifest={}", display_path(&manifest_path, root))?;

    let mut commands = Vec::new();
    for command in &manifest.commands {
        let started_at = current_timestamp();
        writeln!(log)?;
        writeln!(log, "# command_id={}", command.id)?;
        writeln!(log, "# started_at={started_at}")?;
        writeln!(log, "$ {}", command.command)?;
        log.flush()?;

        let argv = resolve_trust_added_command(root, release, &command.command)?;
        let stdout = log.try_clone()?;
        let stderr = log.try_clone()?;
        let mut process = Command::new(&argv[0]);
        process.args(&argv[1..]);
        process.current_dir(root);
        process.stdout(Stdio::from(stdout)).stderr(Stdio::from(stderr));
        process.env("TRUST_STRICT", "1");
        process.env("TRUST_RELEASE_GATE", if release { "1" } else { "0" });
        let started = Instant::now();
        let status = process.status()?;
        let ended_at = current_timestamp();
        let duration_seconds = started.elapsed().as_secs_f64();
        let exit_status = status.code().unwrap_or(-1);
        writeln!(log, "# ended_at={ended_at}")?;
        writeln!(log, "# duration_seconds={duration_seconds:.3}")?;
        writeln!(log, "# exit_status={exit_status}")?;
        log.flush()?;

        commands.push(TrustAddedCommandExecution { command: command.clone(), exit_status });
    }

    Ok(TrustAddedExecution { manifest_path, manifest, log_path, commands })
}

fn format_validation_findings(findings: &[crate::ValidationFinding]) -> String {
    findings
        .iter()
        .map(|finding| format!("  {}: {}", finding.field, finding.message))
        .collect::<Vec<_>>()
        .join("\n")
}

fn reject_trust_added_script_launchers(
    _root: &Path,
    manifest: &TrustAddedTestManifest,
) -> Result<(), PortError> {
    for command in &manifest.commands {
        let argv = parse_native_command_line(&command.command).map_err(|message| {
            PortError::Message(format!(
                "Trust-added proof manifest command '{}' is not a native argv command: {message}",
                command.id
            ))
        })?;
        if argv.is_empty() {
            return Err(PortError::Message(format!(
                "Trust-added proof manifest command '{}' is empty",
                command.id
            )));
        };
        validate_canonical_trust_added_argv(&argv).map_err(|message| {
            PortError::Message(format!(
                "Trust-added proof manifest command '{}' is not canonical: {message}",
                command.id
            ))
        })?;
    }
    Ok(())
}

fn resolve_trust_added_command(
    root: &Path,
    release: bool,
    command: &str,
) -> Result<Vec<String>, PortError> {
    let argv = parse_native_command_line(command).map_err(|message| {
        PortError::Message(format!("Trust-added proof manifest command is invalid: {message}"))
    })?;
    let Some(program) = argv.first() else {
        return Err(PortError::Message("Trust-added proof manifest command is empty".to_string()));
    };
    validate_canonical_trust_added_argv(&argv).map_err(|message| {
        PortError::Message(format!(
            "Trust-added proof manifest command is not canonical: {message}"
        ))
    })?;

    if Path::new(program).file_name().and_then(OsStr::to_str) != Some("targo") {
        return Err(PortError::Message(
            "Trust-added proof manifest command must start with `targo`".to_string(),
        ));
    }

    let mut trust_cargo = resolve_trust_cargo(root, release)?;
    trust_cargo.extend(argv.into_iter().skip(1));
    Ok(trust_cargo)
}

fn validate_canonical_trust_added_argv(argv: &[String]) -> Result<(), String> {
    let prefix = ["targo", "trust", "domination", "trust-added"];
    if argv.len() < prefix.len() + 1
        || !argv.iter().take(prefix.len()).map(String::as_str).eq(prefix)
    {
        return Err(
            "must use `targo trust domination trust-added [--strict] --release <mode>`".to_string()
        );
    }

    let mut strict_seen = false;
    let mut release_seen = false;
    let mut mode = None;
    for arg in &argv[prefix.len()..] {
        match arg.as_str() {
            "--strict" if mode.is_none() && !strict_seen => strict_seen = true,
            "--release" if mode.is_some() => {
                return Err("`--release` must appear before the trust-added mode".to_string());
            }
            "--release" if release_seen => {
                return Err("must contain exactly one pre-mode `--release` flag".to_string());
            }
            "--release" => release_seen = true,
            option if option.starts_with('-') => {
                return Err(format!("unsupported option `{option}`"));
            }
            value if mode.replace(value.to_string()).is_none() => {}
            value => return Err(format!("unexpected trailing argument `{value}`")),
        }
    }

    let Some(mode) = mode else {
        return Err("missing trust-added mode".to_string());
    };
    if !is_canonical_trust_added_mode(&mode) {
        return Err(format!("unknown trust-added mode `{mode}`"));
    }
    if !release_seen {
        return Err("must contain exactly one pre-mode `--release` flag".to_string());
    }
    Ok(())
}

fn is_canonical_trust_added_mode(mode: &str) -> bool {
    matches!(
        mode,
        "quick"
            | "trustc-native"
            | "trust-added-compiletest"
            | "trust-extra"
            | "binary-decompilation-golden"
            | "native-contracts-pipeline-v2"
            | "smoke"
            | "parity"
            | "full"
            | "launch"
            | "public-distribution"
            | "prepublish"
            | "installed"
            | "installed-default"
            | "stage0-lineage"
    )
}

fn parse_native_command_line(command: &str) -> Result<Vec<String>, String> {
    let mut words = Vec::new();
    let mut current = String::new();
    let mut chars = command.chars().peekable();
    let mut quote = None;

    while let Some(ch) = chars.next() {
        match (quote, ch) {
            (None, ch) if ch.is_whitespace() => {
                if !current.is_empty() {
                    words.push(std::mem::take(&mut current));
                }
            }
            (None, '\'' | '"') => quote = Some(ch),
            (Some(active), ch) if ch == active => quote = None,
            (_, '\\') => {
                let Some(next) = chars.next() else {
                    return Err("trailing backslash".to_string());
                };
                current.push(next);
            }
            _ => current.push(ch),
        }
    }

    if let Some(active) = quote {
        return Err(format!("unterminated {active} quote"));
    }
    if !current.is_empty() {
        words.push(current);
    }
    Ok(words)
}

fn combined_execution_exit_status(
    upstream_exit_status: i32,
    trust_added: &TrustAddedExecution,
) -> i32 {
    if upstream_exit_status != 0 {
        return upstream_exit_status;
    }
    trust_added
        .commands
        .iter()
        .find_map(|command| (command.exit_status != 0).then_some(command.exit_status))
        .unwrap_or(0)
}

fn trust_added_exit_status(trust_added: &TrustAddedExecution) -> i32 {
    trust_added
        .commands
        .iter()
        .find_map(|command| (command.exit_status != 0).then_some(command.exit_status))
        .unwrap_or(0)
}

fn rust_bootstrap_command(root: &Path) -> Result<Vec<String>, PortError> {
    if let Ok(configured) = env::var("TRUST_UPSTREAM_RUST_BOOTSTRAP") {
        let command = split_words(&configured);
        if command.is_empty() {
            return Err(PortError::Message("TRUST_UPSTREAM_RUST_BOOTSTRAP is empty".to_string()));
        }
        let command = command
            .into_iter()
            .enumerate()
            .map(|(index, part)| {
                if index == 0 {
                    root_path(root, Path::new(&part)).to_string_lossy().into_owned()
                } else {
                    part
                }
            })
            .collect::<Vec<_>>();
        reject_non_rust_bootstrap_launcher(&command)?;
        return Ok(command);
    }

    for candidate in
        [root.join("build/bootstrap/debug/bootstrap"), root.join("build/bootstrap/bootstrap")]
    {
        if candidate.is_file() {
            return Ok(vec![candidate.to_string_lossy().into_owned()]);
        }
    }

    Err(PortError::Message(
        "Rust bootstrap binary not found; build src/bootstrap or set TRUST_UPSTREAM_RUST_BOOTSTRAP"
            .to_string(),
    ))
}

fn reject_non_rust_bootstrap_launcher(command: &[String]) -> Result<(), PortError> {
    for part in command {
        let file_name = Path::new(part)
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or(part)
            .to_ascii_lowercase();
        let forbidden = file_name == "x.py"
            || file_name == "run_trust_superset_suite.sh"
            || file_name == "sh"
            || file_name == "bash"
            || file_name == "zsh"
            || file_name == "fish"
            || file_name == "python"
            || file_name == "python3"
            || file_name.starts_with("python3.")
            || file_name.starts_with("pypy");
        if forbidden {
            return Err(PortError::Message(format!(
                "TRUST_UPSTREAM_RUST_BOOTSTRAP must name the Rust bootstrap binary, not a Python or shell wrapper: {part}"
            )));
        }
    }
    Ok(())
}

fn proof_inventory_tests(
    max_files: Option<usize>,
    upstream_entries: &[GitTreeEntry],
    exported_paths: &[String],
) -> Vec<ProofUpstreamTest> {
    let upstream_by_path = upstream_entries
        .iter()
        .map(|entry| (entry.path.as_str(), entry))
        .collect::<BTreeMap<_, _>>();
    let all_upstream_paths =
        upstream_entries.iter().map(|entry| entry.path.clone()).collect::<Vec<_>>();
    let source = if max_files.is_some() { exported_paths } else { &all_upstream_paths };
    let primary = unique_primary_paths(source);
    let paths = if primary.is_empty() {
        source.iter().cloned().collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>()
    } else {
        primary
    };
    paths
        .into_iter()
        .enumerate()
        .map(|(index, path)| ProofUpstreamTest {
            id: proof_upstream_test_id(index, &path),
            source_git_blob: upstream_by_path.get(path.as_str()).map(|entry| entry.blob.clone()),
            path,
        })
        .collect()
}

#[allow(clippy::too_many_arguments)] // proof-artifact writer captures the full execution context for each suite
fn write_execution_proof_artifacts(
    root: &Path,
    proof_dir: &Path,
    resolved_revision: &str,
    local_revision: &str,
    proof_tests: &[ProofUpstreamTest],
    upstream_exit_status: i32,
    trust_added: &TrustAddedExecution,
    log_path: &Path,
    execution_command: &str,
    release: bool,
    test_exceptions: &TestExceptionLedger,
    test_exception_validation_date: &str,
) -> Result<(), PortError> {
    let upstream_passed = upstream_exit_status == 0;
    let upstream_artifact = log_path.to_string_lossy().into_owned();
    let trust_added_artifact = trust_added.log_path.to_string_lossy().into_owned();
    let trust_added_inventory_path = display_path(&trust_added.manifest_path, root);
    let trust_added_outcomes = trust_added_proof_outcomes(trust_added);
    let mut inventory_tests = proof_tests
        .iter()
        .map(|test| TestInventoryEntry {
            id: test.id.clone(),
            suite: suite_for_path(&test.path).to_string(),
            path: test.path.clone(),
            revision: Some(resolved_revision.to_string()),
            source_git_blob: test.source_git_blob.clone(),
            source: TestSource::UpstreamRust,
            kind: kind_for_path(&test.path),
            applicable: true,
            inapplicable_reason: None,
            source_sha256: None,
        })
        .collect::<Vec<_>>();
    inventory_tests.extend(trust_added_outcomes.iter().map(|(test_id, outcome)| {
        TestInventoryEntry {
            id: test_id.clone(),
            suite: outcome.command_ids.join("+"),
            path: trust_added_inventory_path.clone(),
            revision: None,
            source_git_blob: None,
            source: TestSource::TrustAdded,
            kind: TestKind::Shell,
            applicable: true,
            inapplicable_reason: None,
            source_sha256: None,
        }
    }));
    let inventory = TestInventory {
        schema_version: crate::SCHEMA_VERSION.to_string(),
        upstream_revision: resolved_revision.to_string(),
        local_revision: local_revision.to_string(),
        host: None,
        tests: inventory_tests,
    };

    let mut results = proof_tests
        .iter()
        .map(|test| {
            let outcome = if upstream_passed { TestOutcome::Passed } else { TestOutcome::Failed };
            TestResult {
                test_id: test.id.clone(),
                outcome,
                exception_id: matching_test_exception_id(test_exceptions, &test.id, outcome),
                observed: Some(if upstream_passed {
                    "upstream bootstrap test run passed".to_string()
                } else {
                    format!("upstream bootstrap exited with {upstream_exit_status}")
                }),
                artifact: Some(upstream_artifact.clone()),
            }
        })
        .collect::<Vec<_>>();
    results.extend(trust_added_outcomes.iter().map(|(test_id, outcome)| {
        let result_outcome = if outcome.failed { TestOutcome::Failed } else { TestOutcome::Passed };
        TestResult {
            test_id: test_id.clone(),
            outcome: result_outcome,
            exception_id: matching_test_exception_id(test_exceptions, test_id, result_outcome),
            observed: Some(if outcome.failed {
                format!("Trust-added command(s) failed: {}", outcome.command_ids.join(", "))
            } else {
                format!("Trust-added command(s) passed: {}", outcome.command_ids.join(", "))
            }),
            artifact: Some(trust_added_artifact.clone()),
        }
    }));
    let generated_on = current_date_string();
    let result_report = TestResultReport {
        schema_version: crate::SCHEMA_VERSION.to_string(),
        inventory_id: "generated-by-trust-domination-upstream-tests".to_string(),
        generated_on: generated_on.clone(),
        command: proof_command_line(execution_command, trust_added),
        results,
    };
    let summary = validate_test_proof_bundle(TestProofBundle {
        inventory: &inventory,
        results: &result_report,
        exceptions: test_exceptions,
        trust_added_tests: (!trust_added.manifest.commands.is_empty())
            .then_some(&trust_added.manifest),
        validation_date: test_exception_validation_date,
        release,
    })
    .unwrap_or_else(|_| proof_totals(&inventory, &result_report));
    write_json(&proof_dir.join("inventory.json"), &serde_json::to_value(&inventory)?)?;
    write_json(&proof_dir.join("results.json"), &serde_json::to_value(&result_report)?)?;
    write_json(&proof_dir.join("proof-summary.json"), &serde_json::to_value(summary)?)
}

fn empty_test_exception_ledger() -> TestExceptionLedger {
    TestExceptionLedger {
        schema_version: crate::SCHEMA_VERSION.to_string(),
        exceptions: Vec::new(),
    }
}

fn matching_test_exception_id(
    test_exceptions: &TestExceptionLedger,
    test_id: &str,
    outcome: TestOutcome,
) -> Option<String> {
    test_exceptions
        .exceptions
        .iter()
        .find(|exception| {
            exception.status == ExceptionStatus::Active
                && exception.test_id == test_id
                && test_exception_kind_accounts_for(outcome, exception.kind)
        })
        .map(|exception| exception.id.clone())
}

fn test_exception_kind_accounts_for(outcome: TestOutcome, kind: TestExceptionKind) -> bool {
    matches!(
        (outcome, kind),
        (TestOutcome::Failed, TestExceptionKind::ExpectedFail)
            | (TestOutcome::Failed, TestExceptionKind::IntentionalDivergence)
            | (TestOutcome::Skipped, TestExceptionKind::ExpectedSkip)
            | (TestOutcome::Skipped, TestExceptionKind::EnvironmentalSkip)
            | (TestOutcome::Diffed, TestExceptionKind::ChangedDiagnostic)
            | (TestOutcome::Diffed, TestExceptionKind::IntentionalDivergence)
    )
}

fn trust_added_inventory_ids(manifest: &TrustAddedTestManifest) -> Vec<String> {
    manifest
        .commands
        .iter()
        .flat_map(|command| command.covers.iter().cloned())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn trust_added_proof_outcomes(
    trust_added: &TrustAddedExecution,
) -> BTreeMap<String, TrustAddedProofOutcome> {
    let command_statuses = trust_added
        .commands
        .iter()
        .map(|command| (command.command.id.as_str(), command.exit_status))
        .collect::<BTreeMap<_, _>>();
    let mut outcomes = BTreeMap::<String, TrustAddedProofOutcome>::new();

    for command in &trust_added.manifest.commands {
        for test_id in &command.covers {
            let outcome = outcomes.entry(test_id.clone()).or_default();
            outcome.command_ids.push(command.id.clone());
            outcome.command_lines.push(command.command.clone());
            if command_statuses.get(command.id.as_str()).copied().unwrap_or(-1) != 0 {
                outcome.failed = true;
            }
        }
    }

    outcomes
}

fn proof_command_line(execution_command: &str, trust_added: &TrustAddedExecution) -> String {
    let mut commands = std::iter::once(execution_command.to_string())
        .chain(trust_added.commands.iter().map(|command| command.command.command.clone()))
        .collect::<Vec<_>>();
    commands.dedup();
    commands.join(" && ")
}

fn proof_upstream_test_id(index: usize, path: &str) -> String {
    format!("upstream.{index:08}.{}", sanitize_proof_id(path))
}

fn sanitize_proof_id(value: &str) -> String {
    value
        .bytes()
        .map(|byte| match byte {
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'.' | b'_' | b':' | b'-' => char::from(byte),
            _ => '.',
        })
        .collect()
}

fn suite_for_path(path: &str) -> &str {
    let mut parts = path.split('/');
    match (parts.next(), parts.next()) {
        (Some("tests"), Some(suite)) => suite,
        (Some("src"), Some("tools")) => "tool",
        (Some("library"), _) => "library",
        _ => "other",
    }
}

fn kind_for_path(path: &str) -> TestKind {
    if path.starts_with("tests/") {
        TestKind::Compiletest
    } else if path.starts_with("library/") {
        TestKind::Rustbuild
    } else if path.contains("/cargo/tests/") {
        TestKind::Cargo
    } else if path.starts_with("src/tools/") {
        TestKind::Tool
    } else {
        TestKind::Other
    }
}

fn proof_totals(inventory: &TestInventory, results: &TestResultReport) -> TestProofTotals {
    let result_by_test = results
        .results
        .iter()
        .map(|result| (result.test_id.as_str(), result))
        .collect::<BTreeMap<_, _>>();
    let mut totals = TestProofTotals { total: inventory.tests.len() as u64, ..Default::default() };
    for test in &inventory.tests {
        match test.source {
            TestSource::UpstreamRust => totals.upstream += 1,
            TestSource::TrustAdded => totals.trust_added += 1,
        }
        match result_by_test.get(test.id.as_str()).map(|result| result.outcome) {
            Some(TestOutcome::Passed) => totals.passed += 1,
            Some(TestOutcome::UpstreamInapplicable) => totals.upstream_inapplicable += 1,
            Some(TestOutcome::Failed | TestOutcome::Skipped | TestOutcome::Diffed) => {
                if result_by_test
                    .get(test.id.as_str())
                    .and_then(|result| result.exception_id.as_ref())
                    .is_some()
                {
                    totals.excepted += 1;
                } else {
                    totals.unaccounted += 1;
                }
            }
            Some(TestOutcome::Unknown) | None => totals.unaccounted += 1,
        }
    }
    totals
}

fn resolve_trust_cargo(root: &Path, require_trust: bool) -> Result<Vec<String>, PortError> {
    if let Ok(configured) = env::var("TRUST_UPSTREAM_COMPAT_CARGO") {
        let command = split_words(&configured);
        if command.is_empty() {
            return Err(PortError::Message("TRUST_UPSTREAM_COMPAT_CARGO is empty".to_string()));
        }
        if require_trust {
            require_release_trust_cargo_command(root, &command, "TRUST_UPSTREAM_COMPAT_CARGO")?;
        }
        return Ok(command);
    }

    if let Ok(targo) = env::var("TRUST_TARGO_BIN") {
        let path = root_path(root, Path::new(&targo));
        validate_targo_path(&path, "TRUST_TARGO_BIN")?;
        return Ok(vec![path.to_string_lossy().into_owned()]);
    }

    if let Some(stage2) = find_repo_stage2_targo(root) {
        return Ok(vec![stage2.to_string_lossy().into_owned()]);
    }

    if require_trust {
        return Err(PortError::Message(
            "release upstream porting requires Trust targo; use build/<host>/stage2/bin/targo or put standalone targo on PATH; ambient cargo is rejected".to_string(),
        ));
    }

    if let Some(targo) = which("targo") {
        return Ok(vec![targo.to_string_lossy().into_owned()]);
    }
    if let Some(cargo) = which("cargo") {
        return Ok(vec![cargo.to_string_lossy().into_owned()]);
    }
    Err(PortError::Message(
        "Trust targo was not found; set TRUST_TARGO_BIN or TRUST_UPSTREAM_COMPAT_CARGO".to_string(),
    ))
}

fn split_words(value: &str) -> Vec<String> {
    value.split_whitespace().map(str::to_string).collect()
}

fn require_release_trust_cargo_command(
    root: &Path,
    command: &[String],
    source: &str,
) -> Result<(), PortError> {
    if let Some(first) = command.first() {
        let path = root_path(root, Path::new(first));
        if path.file_name().and_then(OsStr::to_str) == Some("targo") {
            if env::var("TRUST_TARGO_BIN").ok().is_some_and(|configured| {
                same_path(&path, &root_path(root, Path::new(&configured)))
            }) {
                return Ok(());
            }
            if is_repo_stage2_targo(root, &path) && path.is_file() {
                return Ok(());
            }
        }
    }
    Err(PortError::Message(format!(
        "release upstream porting requires Trust targo; {source} must be build/<host>/stage2/bin/targo or standalone targo on PATH; ambient cargo is rejected"
    )))
}

fn validate_targo_path(path: &Path, source: &str) -> Result<(), PortError> {
    if path.file_name().and_then(OsStr::to_str) != Some("targo") {
        return Err(PortError::Message(format!(
            "{source} must point to a targo binary: {}",
            path.display()
        )));
    }
    if !path.is_file() {
        return Err(PortError::Message(format!("{source} is not executable: {}", path.display())));
    }
    Ok(())
}

fn find_repo_stage2_targo(root: &Path) -> Option<PathBuf> {
    let direct = root.join("build/host/stage2/bin/targo");
    if direct.is_file() {
        return Some(direct);
    }
    let build = root.join("build");
    let entries = fs::read_dir(build).ok()?;
    for entry in entries.flatten() {
        let candidate = entry.path().join("stage2/bin/targo");
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn is_repo_stage2_targo(root: &Path, path: &Path) -> bool {
    let Ok(path) = path.canonicalize() else {
        return false;
    };
    let Ok(build) = root.join("build").canonicalize() else {
        return false;
    };
    path.strip_prefix(build).ok().is_some_and(|relative| relative.ends_with("stage2/bin/targo"))
}

fn which(name: &str) -> Option<PathBuf> {
    let paths = env::var_os("PATH")?;
    for dir in env::split_paths(&paths) {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn current_timestamp() -> String {
    let output = Command::new("date").arg("-u").arg("+%Y-%m-%dT%H:%M:%SZ").output();
    output
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| "1970-01-01T00:00:00Z".to_string())
}

fn current_date_string() -> String {
    current_timestamp().split('T').next().unwrap_or("1970-01-01").to_string()
}

fn write_json(path: &Path, value: &Value) -> Result<(), PortError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut output = serde_json::to_string_pretty(value)?;
    output.push('\n');
    fs::write(path, output)?;
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DocumentFormat {
    Toml,
    Json,
}

fn document_format(path: &Path) -> DocumentFormat {
    match path.extension().and_then(OsStr::to_str) {
        Some(extension) if extension.eq_ignore_ascii_case("json") => DocumentFormat::Json,
        _ => DocumentFormat::Toml,
    }
}

fn display_path(path: &Path, root: &Path) -> String {
    path.strip_prefix(root).unwrap_or(path).to_string_lossy().replace('\\', "/")
}

fn shell_join(args: &[String]) -> String {
    args.iter().map(|arg| shell_quote(arg)).collect::<Vec<_>>().join(" ")
}

fn shell_quote(value: &str) -> String {
    if value.bytes().all(|byte| {
        byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.' | b'/' | b':' | b'=')
    }) {
        value.to_string()
    } else {
        format!("'{}'", value.replace('\'', "'\\''"))
    }
}

fn sha256_bytes(data: &[u8]) -> String {
    let digest = Sha256::digest(data);
    format!("sha256:{digest:x}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        BaselineEntry, BaselineStatus, CompatibilityExpectation, CompatibilitySurface,
        LocalSnapshot, UpstreamSnapshot,
    };

    #[test]
    fn trust_added_executor_requires_exactly_one_pre_mode_release() {
        let argv = |tail: &[&str]| {
            ["targo", "trust", "domination", "trust-added"]
                .into_iter()
                .chain(tail.iter().copied())
                .map(str::to_string)
                .collect::<Vec<_>>()
        };

        assert_eq!(validate_canonical_trust_added_argv(&argv(&["--release", "quick"])), Ok(()));

        for tail in
            [&["quick"][..], &["--release", "--release", "quick"][..], &["quick", "--release"][..]]
        {
            let error = validate_canonical_trust_added_argv(&argv(tail))
                .expect_err("executor must reject a non-release canonical command");
            assert!(error.contains("--release"), "unexpected error for {tail:?}: {error}");
        }
    }

    #[test]
    fn proof_mode_auto_resolves_bounded_runs_to_smoke() {
        assert_eq!(ProofMode::Auto.resolved(Some(1)), ProofMode::Smoke);
        assert_eq!(ProofMode::Auto.resolved(None), ProofMode::Full);
        assert_eq!(ProofMode::Full.resolved(Some(1)), ProofMode::Full);
    }

    #[test]
    fn compatibility_summary_release_evidence_contract_preserves_architecture_provenance() {
        struct Case {
            run_id: &'static str,
            target_arch: &'static str,
            target: &'static str,
            target_triple: &'static str,
            host: &'static str,
            host_triple: &'static str,
            summary_out: &'static str,
            out_dir: &'static str,
        }

        let cases = [
            Case {
                run_id: "compat-x86_64-release-full",
                target_arch: "x86_64",
                target: "x86_64-unknown-linux-gnu",
                target_triple: "x86_64-unknown-linux-gnu",
                host: "x86_64-unknown-linux-gnu",
                host_triple: "x86_64-unknown-linux-gnu",
                summary_out: "reports/strict-superiority/x86_64/upstream-summary.json",
                out_dir: "reports/strict-superiority/x86_64/porting",
            },
            Case {
                run_id: "compat-aarch64-release-full",
                target_arch: "aarch64",
                target: "aarch64-apple-darwin",
                target_triple: "aarch64-apple-darwin",
                host: "aarch64-apple-darwin",
                host_triple: "aarch64-apple-darwin",
                summary_out: "reports/strict-superiority/aarch64/upstream-summary.json",
                out_dir: "reports/strict-superiority/aarch64/porting",
            },
        ];
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let baseline = release_contract_baseline();
        let scorecard = json!({
            "totals": {
                "failed": 0,
                "tool_failures": 0
            },
            "validation_failures": [],
            "proof_artifacts_complete": true
        });

        for case in cases {
            let options = PortOptions {
                repo_root: root.to_path_buf(),
                baseline: PathBuf::from("tests/upstream-rust/baseline.toml"),
                upstream_fixes: PathBuf::from("tests/upstream-rust/upstream-fixes.toml"),
                test_exceptions: None,
                patch_manifest: None,
                llm_directives: None,
                summary_out: Some(PathBuf::from(case.summary_out)),
                run_id: Some(case.run_id.to_string()),
                target_arch: Some(case.target_arch.to_string()),
                target: Some(case.target.to_string()),
                target_triple: Some(case.target_triple.to_string()),
                host: Some(case.host.to_string()),
                host_triple: Some(case.host_triple.to_string()),
                test_exception_validation_date: None,
                upstream_revision: "rust-lang/rust:HEAD".to_string(),
                upstream_remote: "https://github.com/rust-lang/rust.git".to_string(),
                out_dir: PathBuf::from(case.out_dir),
                execute: true,
                apply: false,
                fetch: false,
                scorecard_log: None,
                bootstrap_args: String::new(),
                max_files: None,
                release: true,
                proof_mode: ProofMode::Full,
            };
            let summary = compatibility_summary_from_porting(
                root,
                &baseline,
                &scorecard,
                &options,
                &root.join(case.summary_out),
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
                0,
            )
            .expect("release/full/execute summary should build");
            assert_eq!(summary.run_id.as_deref(), Some(case.run_id));
            assert_eq!(summary.target_arch.as_deref(), Some(case.target_arch));
            assert_eq!(summary.target.as_deref(), Some(case.target));
            assert_eq!(summary.target_triple.as_deref(), Some(case.target_triple));
            assert_eq!(summary.host.as_deref(), Some(case.host));
            assert_eq!(summary.host_triple.as_deref(), Some(case.host_triple));
            assert_eq!(summary.totals.compatible, 1);
            assert_eq!(summary.totals.unknown, 0);

            let value = serde_json::to_value(&summary).expect("summary should serialize");
            let runner = &value["runner"];
            assert_eq!(runner["release"].as_bool(), Some(true));
            assert_eq!(runner["execute"].as_bool(), Some(true));
            assert_eq!(runner["proof_mode"].as_str(), Some("full"));
            assert_eq!(runner["proof_mode_requested"].as_str(), Some("full"));
            assert_eq!(runner["proof_mode_resolved"].as_str(), Some("full"));
            assert_eq!(runner["summary_out"].as_str(), Some(case.summary_out));
            assert_eq!(runner["out_dir"].as_str(), Some(case.out_dir));
            assert_eq!(runner["run_id"].as_str(), Some(case.run_id));
            assert_eq!(runner["target_arch"].as_str(), Some(case.target_arch));
            assert_eq!(runner["target"].as_str(), Some(case.target));
            assert_eq!(runner["target_triple"].as_str(), Some(case.target_triple));
            assert_eq!(runner["host"].as_str(), Some(case.host));
            assert_eq!(runner["host_triple"].as_str(), Some(case.host_triple));

            let argv = json_string_array(&runner["argv"]);
            assert_eq!(
                argv.iter().take(4).map(String::as_str).collect::<Vec<_>>(),
                ["targo", "trust", "domination", "upstream-tests"]
            );
            assert!(argv.iter().any(|arg| arg == "--release"));
            assert!(argv.iter().any(|arg| arg == "--execute"));
            assert!(argv.iter().any(|arg| arg == "--no-apply"));
            assert_eq!(flag_value(&argv, "--proof-mode"), Some("full"));
            assert_eq!(flag_value(&argv, "--summary-out"), Some(case.summary_out));
            assert_eq!(flag_value(&argv, "--out-dir"), Some(case.out_dir));
            assert_eq!(flag_value(&argv, "--run-id"), Some(case.run_id));
            assert_eq!(flag_value(&argv, "--target-arch"), Some(case.target_arch));
            assert_eq!(flag_value(&argv, "--target"), Some(case.target));
            assert_eq!(flag_value(&argv, "--target-triple"), Some(case.target_triple));
            assert_eq!(flag_value(&argv, "--host"), Some(case.host));
            assert_eq!(flag_value(&argv, "--host-triple"), Some(case.host_triple));
            assert_eq!(runner["release_facing_command"].as_str(), Some(shell_join(&argv).as_str()));

            let contract = &runner["release_evidence_contract"];
            assert_eq!(
                contract["entrypoint"].as_str(),
                Some("targo trust domination upstream-tests")
            );
            assert_eq!(contract["requires_release"].as_bool(), Some(true));
            assert_eq!(contract["requires_execute"].as_bool(), Some(true));
            assert_eq!(contract["requires_proof_mode"].as_str(), Some("full"));
            assert_eq!(contract["requires_summary_out"].as_bool(), Some(true));
            assert_eq!(contract["out_dir"].as_str(), Some(case.out_dir));
            assert_eq!(contract["satisfied"].as_bool(), Some(true));
            assert_eq!(contract["run_id"].as_str(), Some(case.run_id));
            assert_eq!(contract["target_arch"].as_str(), Some(case.target_arch));
            assert_eq!(contract["target_triple"].as_str(), Some(case.target_triple));
            assert_eq!(contract["host_triple"].as_str(), Some(case.host_triple));
        }
    }

    #[test]
    fn adapter_rewrites_rustdoc_gui_title_only() {
        let line = r#"store-value: (title, "test_docs - Rust")"#;
        let rewritten =
            apply_adapter_rule("rustdoc_gui_title_brand", "tests/rustdoc-gui/search.goml", line)
                .expect("rule applies");
        assert_eq!(rewritten, r#"store-value: (title, "test_docs - Trust")"#);
        assert!(
            apply_adapter_rule(
                "rustdoc_gui_title_brand",
                "tests/rustdoc-gui/search.goml",
                "# comment mentioning Rust"
            )
            .is_none()
        );
    }

    #[test]
    fn adapter_rewrites_public_trust_compiler_help_names() {
        let explain = "For more information about this error, try `rustc --explain E0703`.\n";
        assert_eq!(
            apply_adapter_rule("explain_tool_name", "tests/ui/abi/demo.stderr", explain)
                .expect("explain rule applies"),
            "For more information about this error, try `trustc --explain E0703`.\n"
        );

        let calling_conventions =
            "   = note: invoke `rustc --print=calling-conventions` for a full list\n";
        assert_eq!(
            apply_adapter_rule(
                "calling_conventions_print_tool_name",
                "tests/ui/abi/demo.stderr",
                calling_conventions,
            )
            .expect("calling-conventions rule applies"),
            "   = note: invoke `trustc --print=calling-conventions` for a full list\n"
        );

        let inline_annotation =
            "//~^^ NOTE invoke `rustc --print=calling-conventions` for a full list\n";
        assert_eq!(
            apply_adapter_rule(
                "calling_conventions_print_tool_name",
                "tests/ui/abi/demo.rs",
                inline_annotation,
            )
            .expect("calling-conventions rule applies to inline expectations"),
            "//~^^ NOTE invoke `trustc --print=calling-conventions` for a full list\n"
        );

        let svg_footer =
            "<tspan>For more information about this error, try `rustc --explain E0061`.</tspan>\n";
        assert_eq!(
            apply_adapter_rule(
                "explain_tool_name",
                "tests/ui/argument-suggestions/demo.svg",
                svg_footer,
            )
            .expect("explain rule applies to svg expectations"),
            "<tspan>For more information about this error, try `trustc --explain E0061`.</tspan>\n"
        );

        assert!(
            apply_adapter_rule(
                "explain_tool_name",
                "tests/ui/abi/demo.rs",
                "// a source comment mentioning `rustc --explain E0000`\n",
            )
            .is_none()
        );
    }

    #[test]
    fn adapter_rewrites_trust_docs_expected_notes() {
        let asm_note = "   = note: see the asm section of Rust By Example <https://doc.rust-lang.org/nightly/rust-by-example/unsafe/asm.html#labels> for more information\n";
        assert_eq!(
            apply_adapter_rule("asm_labels_docs_note", "tests/ui/asm/demo.stderr", asm_note)
                .expect("asm docs note rule applies"),
            "   = note: see the Trust By Example inline assembly labels section for more information\n"
        );

        // Retired rule: `see issue #N <URL>` notes must pass through untouched
        // (the compiler emits the URL; stripping it broke drop-in parity).
        let type_alias_note = "           see issue #112792 <https://github.com/rust-lang/rust/issues/112792> for more information\n";
        assert_eq!(
            apply_adapter_rule(
                "trust_docs_reference_notes",
                "tests/ui/associated-type-bounds/type-alias.stderr",
                type_alias_note,
            )
            .expect("Trust docs reference rule applies"),
            type_alias_note,
        );

        let dyn_note = "   = note: for more information, visit <https://doc.rust-lang.org/reference/items/traits.html#dyn-compatibility>\n";
        assert_eq!(
            apply_adapter_rule("trust_docs_reference_notes", "tests/ui/dyn/demo.stderr", dyn_note)
                .expect("Trust docs reference rule applies"),
            "   = note: for more information, see the Trust Reference's dyn compatibility section\n"
        );

        let check_cfg_note = "   = note: see <https://doc.rust-lang.org/nightly/rustc/check-cfg.html> for more information about checking conditional configuration\n";
        assert_eq!(
            apply_adapter_rule(
                "trust_docs_reference_notes",
                "tests/rustdoc-ui/check-cfg.stderr",
                check_cfg_note,
            )
            .expect("Trust docs reference rule applies"),
            "   = note: see the Trust trustc check-cfg documentation for more information about checking conditional configuration\n"
        );

        let edition_note =
            "   = note: for more on editions, read https://doc.rust-lang.org/edition-guide\n";
        assert_eq!(
            apply_adapter_rule(
                "trust_docs_reference_notes",
                "tests/ui/async-await/edition-2015.stderr",
                edition_note,
            )
            .expect("Trust docs reference rule applies"),
            "   = note: for more on editions, read the Trust Edition Guide\n"
        );

        let edition_help = "   = help: pass `--edition 2024` to `rustc`\n";
        assert_eq!(
            apply_adapter_rule(
                "trust_docs_reference_notes",
                "tests/ui/async-await/edition-2015.stderr",
                edition_help,
            )
            .expect("Trust docs reference rule applies"),
            "   = help: pass `--edition 2024` to `trustc`\n"
        );

        let extern_note = "   = note: for more information, visit https://doc.rust-lang.org/std/keyword.extern.html\n";
        assert_eq!(
            apply_adapter_rule(
                "trust_docs_reference_notes",
                "tests/ui/extern/extern-const.stderr",
                extern_note,
            )
            .expect("Trust docs reference rule applies"),
            "   = note: for more information, see the Trust standard library `extern` keyword documentation\n"
        );

        let variance_note = "   = help: see <https://doc.rust-lang.org/nomicon/subtyping.html> for more information about variance\n";
        assert_eq!(
            apply_adapter_rule(
                "trust_docs_reference_notes",
                "tests/ui/variance/demo.stderr",
                variance_note,
            )
            .expect("Trust docs reference rule applies"),
            "   = help: see the Trust Nomicon's subtyping section for more information about variance\n"
        );

        let lint_note =
            "   = help: a lint with a similar name exists in `rustc` lints: `unused_imports`\n";
        assert_eq!(
            apply_adapter_rule(
                "trust_docs_reference_notes",
                "tests/ui/lint/demo.stderr",
                lint_note,
            )
            .expect("Trust docs reference rule applies"),
            "   = help: a lint with a similar name exists in `trustc` lints: `unused_imports`\n"
        );

        let issue_note = "   = note: see issue #55436 <https://github.com/rust-lang/rust/issues/55436> for more information\n";
        assert_eq!(
            apply_adapter_rule(
                "trust_docs_reference_notes",
                "tests/ui/issues/demo.stderr",
                issue_note,
            )
            .expect("Trust docs reference rule applies"),
            issue_note,
        );
    }

    #[test]
    fn git_status_porcelain_paths_extracts_renames_and_quoted_paths() {
        assert_eq!(
            git_status_porcelain_paths(" M tests/ui/demo.stderr"),
            vec!["tests/ui/demo.stderr"]
        );
        assert_eq!(
            git_status_porcelain_paths("R  tests/ui/old.stderr -> tests/ui/new.stderr"),
            vec!["tests/ui/old.stderr", "tests/ui/new.stderr"]
        );
        assert_eq!(
            git_status_porcelain_paths("?? \"tests/ui/path with spaces.stderr\""),
            vec!["tests/ui/path with spaces.stderr"]
        );
    }

    #[test]
    fn patch_manifest_reapplies_reviewed_replacements_with_audit() {
        let root =
            env::temp_dir().join(format!("trust-upstream-port-patches-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        let ported = root.join("ported");
        let test_file = ported.join("tests/ui/demo.stderr");
        fs::create_dir_all(test_file.parent().expect("test file parent")).expect("create dirs");
        fs::write(&test_file, "error: upstream wording\n").expect("write test file");

        let manifest = root.join("tests/upstream-rust/patches.toml");
        fs::create_dir_all(manifest.parent().expect("manifest parent"))
            .expect("create manifest dir");
        fs::write(
            &manifest,
            r#"
schema_version = "0.1.0"

[[patches]]
id = "trust.test.demo"
status = "active"
owner = "@trust-release"
reason = "fixture Trust wording"
issue = "https://example.invalid/trust/patch-demo"
reviewed_on = "2026-05-07"
expires_on = "2026-08-05"
path = "tests/ui/demo.stderr"
kind = "string-replace"
find = "upstream wording"
replace = "Trust wording"
expected_replacements = 1
"#,
        )
        .expect("write manifest");

        let audit = root.join("adapter-audit.jsonl");
        let report = apply_patch_manifest(&root, &ported, &manifest, "2026-05-07", &audit)
            .expect("apply manifest");

        assert_eq!(
            fs::read_to_string(&test_file).expect("read test file"),
            "error: Trust wording\n"
        );
        assert_eq!(report.active_patch_ids, vec!["trust.test.demo"]);
        assert_eq!(report.applied_patch_ids, vec!["trust.test.demo"]);
        assert_eq!(report.records.len(), 2);
        let audit_text = fs::read_to_string(&audit).expect("read audit");
        assert!(audit_text.contains("patch_manifest:trust.test.demo"));
        assert!(audit_text.contains("patch_manifest:trust.test.demo:file_digest"));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn scorecard_parser_captures_failure_and_tool_rows() {
        let dir =
            env::temp_dir().join(format!("trust-upstream-port-scorecard-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        let log = dir.join("log.txt");
        fs::write(
            &log,
            "[ui] tests/ui/demo.rs ... F\n\
             ---- [ui] tests/ui/demo.rs stdout ----\n\
             Saved the actual stderr to `/tmp/demo.stderr`\n\
             diff of stderr:\n\
             - error: expected\n\
             + error: actual\n\
             The actual stderr differed from the expected stderr\n\
             To only update this specific test, also pass `--test-args demo.rs`\n\
             ---- [ui] tests/ui/demo.rs stdout end ----\n\
             tidy [deps]: FAIL\n\
             error: could not compile `rustdoc` (lib) due to 2 previous errors\n",
        )
        .expect("write log");
        let scorecard =
            parse_scorecard(&log, &empty_test_exception_ledger(), "2026-01-01").expect("scorecard");
        assert_eq!(scorecard_total(&scorecard, "failed"), 1);
        assert_eq!(scorecard_total(&scorecard, "tool_failures"), 2);
        let failed = scorecard["failed_tests"].as_array().expect("failed tests");
        assert_eq!(failed[0]["category"], "diagnostic-drift");
        assert!(failed[0]["detail_available"].as_bool().unwrap());
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn scorecard_nets_active_intentional_divergence_from_failed_total() {
        let dir = env::temp_dir()
            .join(format!("trust-upstream-port-scorecard-net-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        let log = dir.join("log.txt");
        fs::write(&log, "[crashes] tests/crashes/135122.rs ... F\n").expect("write log");
        let ledger = TestExceptionLedger {
            schema_version: crate::SCHEMA_VERSION.to_string(),
            exceptions: vec![crate::TestException {
                id: "test-exc.crashes.135122.no-ice".to_string(),
                test_id: "upstream.00001212.tests.crashes.135122.rs".to_string(),
                suite: "crashes".to_string(),
                path: "tests/crashes/135122.rs".to_string(),
                revision: None,
                kind: TestExceptionKind::IntentionalDivergence,
                status: ExceptionStatus::Active,
                owner: "@trust-release".to_string(),
                reason: "tRust emits ordinary diagnostics instead of the upstream ICE".to_string(),
                issue: "https://github.com/rust-lang/rust/issues/135122".to_string(),
                introduced_by: None,
                reviewed_on: "2026-07-10".to_string(),
                expires_on: "2026-07-28".to_string(),
                allowed_patterns: Vec::new(),
            }],
        };
        // Active + non-expired -> netted out of totals.failed, still listed as excepted.
        let sc = parse_scorecard(&log, &ledger, "2026-07-12").expect("scorecard");
        assert_eq!(scorecard_total(&sc, "failed"), 0);
        assert_eq!(scorecard_total(&sc, "excepted"), 1);
        let failed = sc["failed_tests"].as_array().expect("failed tests");
        assert_eq!(failed[0]["excepted"], true);
        assert_eq!(failed[0]["exception_id"], "test-exc.crashes.135122.no-ice");
        // Expired exception (validation_date past expires_on) must NOT net.
        let sc_expired = parse_scorecard(&log, &ledger, "2026-08-01").expect("scorecard");
        assert_eq!(scorecard_total(&sc_expired, "failed"), 1);
        assert_eq!(scorecard_total(&sc_expired, "excepted"), 0);
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn scorecard_exit_code_fails_on_nonzero_execution_status() {
        let scorecard = json!({
            "totals": {"failed": 0, "tool_failures": 0},
        });

        assert_eq!(scorecard_exit_code(&scorecard, true, Some(101), &[]), 1);
        assert_eq!(scorecard_exit_code(&scorecard, true, Some(0), &[]), 0);
    }

    #[test]
    fn proof_artifact_validation_rejects_empty_ids() {
        let dir = env::temp_dir().join(format!("trust-upstream-port-proof-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        write_json(&dir.join("inventory.json"), &json!({"tests": [{"id": ""}]}))
            .expect("write inventory");
        write_json(&dir.join("results.json"), &json!({"results": [{"test_id": ""}]}))
            .expect("write results");
        write_json(
            &dir.join("proof-summary.json"),
            &json!({
                "total": 1,
                "upstream": 1,
                "trust_added": 0,
                "passed": 1,
                "upstream_inapplicable": 0,
                "excepted": 0,
                "unaccounted": 0,
            }),
        )
        .expect("write proof summary");

        let exceptions = empty_test_exception_ledger();
        let validation = proof_artifact_validation(&dir, false, &exceptions, "2026-04-29", false)
            .expect("validate proof artifacts");
        assert!(!validation["complete"].as_bool().unwrap());
        let invalid = validation["invalid"].as_array().expect("invalid artifacts");
        assert!(invalid.iter().any(|value| value.as_str() == Some("inventory.json")));
        assert!(invalid.iter().any(|value| value.as_str() == Some("results.json")));
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn proof_artifact_validation_uses_supplied_test_exceptions() {
        let dir = env::temp_dir()
            .join(format!("trust-upstream-port-proof-exceptions-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        let test_id = "upstream.00000000.tests.ui.proof.rs";
        let revision = "rust-lang/rust:feedface";
        let inventory = TestInventory {
            schema_version: crate::SCHEMA_VERSION.to_string(),
            upstream_revision: revision.to_string(),
            local_revision: "trust:test".to_string(),
            host: None,
            tests: vec![TestInventoryEntry {
                id: test_id.to_string(),
                suite: "ui".to_string(),
                path: "tests/ui/proof.rs".to_string(),
                revision: Some(revision.to_string()),
                source_git_blob: None,
                source: TestSource::UpstreamRust,
                kind: TestKind::Compiletest,
                applicable: true,
                inapplicable_reason: None,
                source_sha256: None,
            }],
        };
        let results = TestResultReport {
            schema_version: crate::SCHEMA_VERSION.to_string(),
            inventory_id: "fixture".to_string(),
            generated_on: "2026-04-29".to_string(),
            command: "bootstrap test --trust-vanilla".to_string(),
            results: vec![TestResult {
                test_id: test_id.to_string(),
                outcome: TestOutcome::Failed,
                exception_id: Some("test-exc.proof".to_string()),
                observed: Some("fixture failure".to_string()),
                artifact: None,
            }],
        };
        let summary = TestProofTotals {
            total: 1,
            upstream: 1,
            trust_added: 0,
            passed: 0,
            upstream_inapplicable: 0,
            excepted: 1,
            unaccounted: 0,
        };
        let exceptions = TestExceptionLedger {
            schema_version: crate::SCHEMA_VERSION.to_string(),
            exceptions: vec![crate::TestException {
                id: "test-exc.proof".to_string(),
                test_id: test_id.to_string(),
                suite: "ui".to_string(),
                path: "tests/ui/proof.rs".to_string(),
                revision: Some(revision.to_string()),
                kind: TestExceptionKind::ExpectedFail,
                status: ExceptionStatus::Active,
                owner: "@trust-release".to_string(),
                reason: "fixture expected failure".to_string(),
                issue: "https://example.invalid/trust/1".to_string(),
                introduced_by: None,
                reviewed_on: "2026-04-29".to_string(),
                expires_on: "2026-07-28".to_string(),
                allowed_patterns: Vec::new(),
            }],
        };

        write_json(&dir.join("inventory.json"), &serde_json::to_value(inventory).unwrap())
            .expect("write inventory");
        write_json(&dir.join("results.json"), &serde_json::to_value(results).unwrap())
            .expect("write results");
        write_json(&dir.join("proof-summary.json"), &serde_json::to_value(summary).unwrap())
            .expect("write proof summary");

        let validation = proof_artifact_validation(&dir, false, &exceptions, "2026-04-29", false)
            .expect("validate proof artifacts");
        assert!(validation["complete"].as_bool().unwrap());
        assert!(validation["invalid"].as_array().is_some_and(Vec::is_empty));
        assert_eq!(validation["summary_totals"]["excepted"].as_u64(), Some(1));
        assert_eq!(validation["summary_totals"]["unaccounted"].as_u64(), Some(0));
        let _ = fs::remove_dir_all(dir);
    }

    fn release_contract_baseline() -> CompatibilityBaseline {
        CompatibilityBaseline {
            schema_version: crate::SCHEMA_VERSION.to_string(),
            id: "baseline.release-contract".to_string(),
            upstream: UpstreamSnapshot {
                channel: "nightly".to_string(),
                revision: "rust-lang/rust:HEAD".to_string(),
                snapshot_date: None,
            },
            local: LocalSnapshot {
                revision: "trust:HEAD".to_string(),
                branch: None,
                workspace: None,
            },
            entries: vec![BaselineEntry {
                id: "upstream-tests.full-suite".to_string(),
                title: "Full upstream Rust test suite".to_string(),
                surface: CompatibilitySurface::Cli,
                upstream_artifact: "tests/".to_string(),
                local_artifact: Some("tests/".to_string()),
                expectation: CompatibilityExpectation {
                    upstream_behavior: "Rust upstream tests pass".to_string(),
                    local_behavior: "Trust release runner passes the same tests".to_string(),
                    compatibility_rule: "full release execution has no failures".to_string(),
                },
                status: BaselineStatus::Compatible,
                labels: vec!["release-evidence".to_string()],
            }],
        }
    }

    fn json_string_array(value: &Value) -> Vec<String> {
        value
            .as_array()
            .expect("value should be an array")
            .iter()
            .map(|value| value.as_str().expect("array item should be a string").to_string())
            .collect()
    }

    fn flag_value<'a>(argv: &'a [String], flag: &str) -> Option<&'a str> {
        argv.windows(2).find_map(|window| (window[0] == flag).then(|| window[1].as_str()))
    }
}
