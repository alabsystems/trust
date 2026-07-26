//! Rust-native dependency alignment support for `targo trust deps`.
//!
//! This crate keeps dependency snapshot accounting in Rust so the public
//! workflow does not accrete one-off Python scripts.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};
use std::io::{BufRead, BufReader, Read, Write};
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

const LOCK_SCHEMA: &str = "trust.engines.lock.v2";
/// Where sibling engine repos are expected to be cloned. Override with
/// `TRUST_CLONE_ROOT`; defaults to the user's home directory.
const CLONE_ROOT_ENV: &str = "TRUST_CLONE_ROOT";
/// Override for the preferred `trust-wp` main worktree location; defaults to
/// `<clone root>/dependency-worktrees/trust-wp-main`.
const TRUST_WP_MAIN_WORKTREE_ENV: &str = "TRUST_WP_MAIN_WORKTREE";

fn default_clone_root() -> PathBuf {
    if let Some(root) = std::env::var_os(CLONE_ROOT_ENV) {
        return PathBuf::from(root);
    }
    std::env::var_os("HOME")
        .or_else(|| std::env::var_os("USERPROFILE"))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."))
}
const SNAPSHOT_EXCLUDED_ROOT_FILES: &[&str] = &[
    ".dscan.toml",
    ".gitignore",
    ".gitattributes",
    ".gitleaks.toml",
    ".mcp.json",
    ".ownership_conflicts.log.lock",
    ".pre-commit-config.yaml",
    ".scoped_test_index.json",
    ".sync_manifest",
    ".test_state.json",
    ".test_state.json.lock",
    ".test_registry.json",
    "AGENTS.md",
    "CLAUDE.md",
    "GEMINI.md",
    "rust_out",
];
const SNAPSHOT_EXCLUDED_FILE_NAMES: &[&str] = &[
    ".gitattributes",
    ".gitmodules",
    "AGENTS.md",
    "CLAUDE.md",
    "GEMINI.md",
    "Session.vim",
    "session.vim",
];
const SNAPSHOT_EXCLUDED_FILE_SUFFIXES: &[&str] = &[".log", ".rlib"];
const SNAPSHOT_EXCLUDED_PREFIXES: &[&str] = &[
    ".cargo/",
    ".claude/",
    ".github/",
    ".issues/",
    ".pre-commit-local.d/",
    "benchmarks/templates/",
    "metrics/",
    "reports/",
    "target-fallback-test/",
    "templates/",
    "worker_logs/",
];
const SNAPSHOT_EXCLUDED_PATH_COMPONENTS: &[&str] = &[".claude", ".github", ".vscode"];
const OWNED_GITHUB_ORGS: &[&str] = &["alabsystems", "alabsystems", "alabsystems"];
const OWNED_GITHUB_REPOS: &[&str] =
    &["trust_ir", "trust-cg", "ay", "ty", "trust-vc", "trust-wp", "trust-mc", "trust"];

#[derive(Debug, Clone, Copy)]
struct DependencySpec {
    name: &'static str,
    display_name: &'static str,
    source_path: &'static str,
    default_clone_dir: &'static str,
}

const DEPENDENCIES: &[DependencySpec] = &[
    DependencySpec {
        name: "trust_ir",
        display_name: "TrustIr",
        source_path: "third_party/trust_ir",
        default_clone_dir: "TrustIr",
    },
    DependencySpec {
        name: "trust-cg",
        display_name: "trust-cg",
        source_path: "first-party/trust-cg",
        default_clone_dir: "trust-cg",
    },
    DependencySpec {
        name: "trust-mc",
        display_name: "trust-mc",
        source_path: "../trust-mc",
        default_clone_dir: "trust-mc",
    },
    DependencySpec {
        name: "trust-wp",
        display_name: "trust-wp",
        source_path: "first-party/trust-wp",
        default_clone_dir: "trust-wp",
    },
    DependencySpec {
        name: "trust-vc",
        display_name: "trust-vc",
        source_path: "first-party/trust-vc",
        default_clone_dir: "trust-vc",
    },
    DependencySpec {
        name: "ty",
        display_name: "TY",
        source_path: "first-party/ty",
        default_clone_dir: "ty",
    },
    DependencySpec {
        name: "ay",
        display_name: "ay",
        source_path: "first-party/ay",
        default_clone_dir: "ay",
    },
];

#[derive(Debug, Clone)]
pub struct StatusOptions {
    pub root: PathBuf,
    pub lock_file: PathBuf,
    pub clone_root: PathBuf,
    pub dependencies: Vec<String>,
    pub fetch: bool,
    pub deep_hash: bool,
}

impl StatusOptions {
    pub fn for_root(root: impl Into<PathBuf>) -> Self {
        let root = root.into();
        Self {
            lock_file: root.join("trust-engines.lock"),
            root,
            clone_root: default_clone_root(),
            dependencies: Vec::new(),
            fetch: false,
            deep_hash: false,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct AlignmentReport {
    pub schema: &'static str,
    pub root: String,
    pub lock_file: String,
    pub fetch: bool,
    pub summary: AlignmentSummary,
    pub dependencies: Vec<DependencyStatus>,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct AlignmentSummary {
    pub total: usize,
    pub ok: usize,
    pub failed: usize,
    pub stale_lock: usize,
    pub snapshot_mismatch: usize,
    pub live_clone_misaligned: usize,
    pub dirty_live_clone: usize,
    pub metadata_mismatch: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct DependencyStatus {
    pub name: String,
    pub display_name: String,
    pub source_path: String,
    pub remote: Option<String>,
    pub lock_rev: Option<String>,
    pub lock_status: Option<String>,
    pub lock_source_snapshot: Option<String>,
    pub computed_source_snapshot: Option<String>,
    pub computed_source_fingerprint: Option<String>,
    pub source_snapshot_status: SnapshotStatus,
    pub clone_path: String,
    pub clone_exists: bool,
    pub clone_head: Option<String>,
    pub origin_main: Option<String>,
    pub live_clone_status: LiveCloneStatus,
    pub lock_current: bool,
    pub errors: Vec<String>,
    pub actions: Vec<AlignmentAction>,
}

impl DependencyStatus {
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
            && !self.source_snapshot_status.is_blocking()
            && self.live_clone_status == LiveCloneStatus::Aligned
            && self.lock_current
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum SnapshotStatus {
    Aligned,
    Mismatch,
    Missing,
    Error,
    Unchecked,
}

impl SnapshotStatus {
    fn is_blocking(self) -> bool {
        matches!(self, Self::Mismatch | Self::Missing | Self::Error | Self::Unchecked)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum LiveCloneStatus {
    Aligned,
    Missing,
    NotGitWorktree,
    Dirty,
    StaleCheckout,
    FetchFailed,
    Unknown,
}

#[derive(Debug, Clone, Serialize)]
pub struct AlignmentAction {
    pub code: &'static str,
    pub blocking: bool,
    pub summary: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct PlannedMutationReport {
    pub schema: &'static str,
    pub command: String,
    pub apply_requested: bool,
    pub status: &'static str,
    pub reason: String,
    pub required_before_apply: Vec<&'static str>,
}

#[derive(Debug, Clone)]
pub struct MutationOptions {
    pub root: PathBuf,
    pub lock_file: PathBuf,
    pub clone_root: PathBuf,
    pub fetch: bool,
    pub apply: bool,
    pub output_dir: Option<PathBuf>,
    pub dependencies: Vec<String>,
    pub allow_overwrite_local_drift: bool,
    pub overlay_policy: OverlayPolicy,
}

impl MutationOptions {
    pub fn for_root(root: impl Into<PathBuf>) -> Self {
        let root = root.into();
        Self {
            lock_file: root.join("trust-engines.lock"),
            root,
            clone_root: default_clone_root(),
            fetch: false,
            apply: false,
            output_dir: None,
            dependencies: Vec::new(),
            allow_overwrite_local_drift: false,
            overlay_policy: OverlayPolicy::Forbid,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum OverlayPolicy {
    Forbid,
    Bootstrap,
}

impl OverlayPolicy {
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "forbid" => Some(Self::Forbid),
            "bootstrap" => Some(Self::Bootstrap),
            _ => None,
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Self::Forbid => "forbid",
            Self::Bootstrap => "bootstrap",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct MutationReport {
    pub schema: &'static str,
    pub command: String,
    pub apply_requested: bool,
    pub overlay_policy: OverlayPolicy,
    pub root: String,
    pub lock_file: String,
    pub output_dir: Option<String>,
    pub summary: MutationSummary,
    pub dependencies: Vec<MutationDependencyReport>,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct MutationSummary {
    pub total: usize,
    pub ok: usize,
    pub failed: usize,
    pub changed: usize,
    pub artifacts_written: usize,
    pub lock_updated: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct MutationDependencyReport {
    pub name: String,
    pub display_name: String,
    pub source_path: String,
    pub clone_path: String,
    pub clone_head: Option<String>,
    pub origin_main: Option<String>,
    pub status: String,
    pub changed: bool,
    pub file_count: usize,
    pub executable_count: usize,
    pub total_bytes: u64,
    pub source_snapshot: Option<String>,
    pub lock_updated: bool,
    pub artifacts: Vec<String>,
    pub errors: Vec<String>,
    pub actions: Vec<AlignmentAction>,
}

impl MutationDependencyReport {
    fn ok(&self) -> bool {
        self.errors.is_empty()
    }
}

#[derive(Debug)]
pub enum DepsError {
    Io { path: PathBuf, source: std::io::Error },
    Toml { path: PathBuf, source: toml::de::Error },
    InvalidLock(String),
    Git(String),
    Json(serde_json::Error),
}

impl fmt::Display for DepsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Toml { path, source } => write!(f, "{}: {source}", path.display()),
            Self::InvalidLock(message) => write!(f, "{message}"),
            Self::Git(message) => write!(f, "{message}"),
            Self::Json(source) => write!(f, "{source}"),
        }
    }
}

impl std::error::Error for DepsError {}

#[derive(Debug, Deserialize)]
struct LockFile {
    schema: String,
    generated_vendor: Option<GeneratedVendor>,
    #[serde(default)]
    engine: Vec<Engine>,
    #[serde(default)]
    owned_dependency: Vec<OwnedDependency>,
}

#[derive(Debug, Clone, Deserialize)]
struct GeneratedVendor {
    policy: String,
    consistency_hook: String,
}

#[derive(Debug, Clone, Deserialize)]
struct Engine {
    name: String,
    role: String,
    repo: String,
    ref_kind: String,
    rev: String,
    api: String,
    vendor_path: String,
    vendor_snapshot: String,
}

#[derive(Debug, Clone, Deserialize)]
struct OwnedDependency {
    name: String,
    display_name: String,
    role: String,
    remote: String,
    ref_kind: String,
    rev: String,
    path: String,
    source_snapshot: String,
    status: String,
}

#[derive(Debug, Deserialize)]
struct ReleaseManifest {
    policy: Option<ReleasePolicy>,
    #[serde(default)]
    repos: Vec<ReleaseRepo>,
}

#[derive(Debug, Deserialize)]
struct ReleasePolicy {
    canonical_public_owner: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
struct ReleaseRepo {
    id: String,
    snapshot_path: String,
    source_snapshot_sha256: String,
    public_repo: String,
    status: String,
}

#[derive(Debug, Default)]
struct MetadataContext {
    load_errors: Vec<String>,
    readme_rows: BTreeMap<String, ReadmeSnapshotRow>,
    release_repos: BTreeMap<String, ReleaseRepo>,
    canonical_public_owner: Option<String>,
}

#[derive(Debug, Clone)]
struct ReadmeSnapshotRow {
    path: String,
    rev: String,
}

#[derive(Debug, Clone)]
struct GitOutput {
    status: i32,
    stdout: String,
    stderr: String,
}

pub fn collect_status(options: &StatusOptions) -> Result<AlignmentReport, DepsError> {
    let lock = load_lock(&options.lock_file)?;
    if lock.schema != LOCK_SCHEMA {
        return Err(DepsError::InvalidLock(format!(
            "{} schema is {:?}, expected {LOCK_SCHEMA:?}",
            options.lock_file.display(),
            lock.schema
        )));
    }

    let lock_by_name: BTreeMap<String, OwnedDependency> = lock
        .owned_dependency
        .into_iter()
        .map(|dependency| (dependency.name.clone(), dependency))
        .collect();

    let specs = selected_specs(&options.dependencies)?;
    let metadata = load_metadata_context(&options.root);
    let mut dependencies = Vec::with_capacity(specs.len());
    for spec in specs {
        dependencies.push(inspect_dependency(spec, &lock_by_name, options, &metadata));
    }

    let mut summary = AlignmentSummary { total: dependencies.len(), ..AlignmentSummary::default() };
    for dependency in &dependencies {
        if dependency.ok() {
            summary.ok += 1;
        } else {
            summary.failed += 1;
        }
        if !dependency.lock_current {
            summary.stale_lock += 1;
        }
        if dependency.source_snapshot_status.is_blocking() {
            summary.snapshot_mismatch += 1;
        }
        if dependency.live_clone_status != LiveCloneStatus::Aligned {
            summary.live_clone_misaligned += 1;
        }
        if dependency.live_clone_status == LiveCloneStatus::Dirty {
            summary.dirty_live_clone += 1;
        }
        if dependency.errors.iter().any(|error| error.starts_with("metadata:")) {
            summary.metadata_mismatch += 1;
        }
    }

    Ok(AlignmentReport {
        schema: "trust.deps.alignment.v1",
        root: options.root.display().to_string(),
        lock_file: options.lock_file.display().to_string(),
        fetch: options.fetch,
        summary,
        dependencies,
    })
}

pub fn render_text(report: &AlignmentReport) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "Trust dependency alignment: {} ok, {} failed, {} total",
        report.summary.ok, report.summary.failed, report.summary.total
    );
    let _ = writeln!(
        out,
        "stale_lock={} snapshot_mismatch={} live_clone_misaligned={} dirty_live_clone={} metadata_mismatch={}",
        report.summary.stale_lock,
        report.summary.snapshot_mismatch,
        report.summary.live_clone_misaligned,
        report.summary.dirty_live_clone,
        report.summary.metadata_mismatch
    );
    for dependency in &report.dependencies {
        let _ = writeln!(out, "\n{} ({})", dependency.display_name, dependency.name);
        let _ = writeln!(out, "  source: {}", dependency.source_path);
        let _ =
            writeln!(out, "  lock_rev: {}", dependency.lock_rev.as_deref().unwrap_or("<missing>"));
        let _ = writeln!(
            out,
            "  lock_status: {}",
            dependency.lock_status.as_deref().unwrap_or("<missing>")
        );
        let _ = writeln!(
            out,
            "  origin_main: {}",
            dependency.origin_main.as_deref().unwrap_or("<missing>")
        );
        let _ = writeln!(out, "  snapshot: {:?}", dependency.source_snapshot_status);
        if let Some(fingerprint) = &dependency.computed_source_fingerprint {
            let _ = writeln!(out, "  fast_fingerprint: {fingerprint}");
        }
        let _ = writeln!(out, "  live_clone: {:?}", dependency.live_clone_status);
        for error in &dependency.errors {
            let _ = writeln!(out, "  error: {error}");
        }
        for action in &dependency.actions {
            let _ = writeln!(out, "  action: {} - {}", action.code, action.summary);
        }
    }
    out
}

pub fn render_json(report: &AlignmentReport) -> Result<String, DepsError> {
    serde_json::to_string_pretty(report).map_err(DepsError::Json)
}

pub fn planned_mutation(command: &str, apply_requested: bool) -> PlannedMutationReport {
    PlannedMutationReport {
        schema: "trust.deps.planned-mutation.v1",
        command: command.to_string(),
        apply_requested,
        status: if apply_requested { "blocked_not_implemented" } else { "planned" },
        reason: format!(
            "`targo trust deps {command}` is reserved for the transaction path; \
             Wave 1 implements read-only status/diff/upstream-plan/validate first"
        ),
        required_before_apply: vec![
            "git-object based diff classification",
            "deterministic export from dependency origin/main",
            "baggage and symlink rejection policy",
            "atomic third_party snapshot replacement",
            "trust-engines.lock rev/hash co-update",
            "post-import validation evidence",
        ],
    }
}

pub fn render_planned_mutation_text(report: &PlannedMutationReport) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "targo trust deps {}: {}", report.command, report.status);
    let _ = writeln!(out, "{}", report.reason);
    let _ = writeln!(out, "required before apply:");
    for requirement in &report.required_before_apply {
        let _ = writeln!(out, "- {requirement}");
    }
    out
}

pub fn run_export_transaction(options: &MutationOptions) -> Result<MutationReport, DepsError> {
    let lock = load_lock(&options.lock_file)?;
    validate_lock_schema(&lock, &options.lock_file)?;
    let lock_by_name = lock_by_name(lock.owned_dependency.clone());
    let specs = selected_specs(&options.dependencies)?;
    let mut dependencies = Vec::with_capacity(specs.len());
    let mut artifacts_written = 0;
    let output_dir = options.output_dir.clone();

    if options.apply {
        let Some(dir) = &output_dir else {
            return Err(DepsError::InvalidLock(
                "targo trust deps export --apply requires --out DIR".to_string(),
            ));
        };
        std::fs::create_dir_all(dir)
            .map_err(|source| DepsError::Io { path: dir.clone(), source })?;
    }

    for spec in specs {
        let mut report = base_mutation_dependency_report(spec, &lock_by_name, options);
        if let Err(error) = ensure_live_clone_ready(&report, options.fetch) {
            report.errors.push(error);
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        }
        if let Err(error) = ensure_vendor_target_clean(&options.root, &report.source_path) {
            report.errors.push(error);
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        }

        let temp = tempfile::Builder::new()
            .prefix("trust-deps-export-")
            .tempdir()
            .map_err(|source| DepsError::Io { path: std::env::temp_dir(), source })?;
        let origin_dir = temp.path().join("origin").join(spec.name);
        let vendor_dir = temp.path().join("vendor").join(spec.name);
        let origin_summary = match copy_dependency_origin_tree_with_policy(
            spec,
            Path::new(&report.clone_path),
            &origin_dir,
            options.overlay_policy,
        ) {
            Ok(summary) => summary,
            Err(error) => {
                report.errors.push(error);
                report.status = "blocked".to_string();
                dependencies.push(report);
                continue;
            }
        };
        let vendor_summary =
            match copy_git_tracked_tree(&options.root, Some(&report.source_path), &vendor_dir) {
                Ok(summary) => summary,
                Err(error) => {
                    report.errors.push(error);
                    report.status = "blocked".to_string();
                    dependencies.push(report);
                    continue;
                }
            };
        report.file_count = vendor_summary.file_count;
        report.executable_count = vendor_summary.executable_count;
        report.total_bytes = vendor_summary.total_bytes;
        report.source_snapshot = match snapshot_directory(&vendor_dir) {
            Ok(snapshot) => Some(snapshot),
            Err(error) => {
                report.errors.push(error);
                report.status = "blocked".to_string();
                dependencies.push(report);
                continue;
            }
        };

        let diff = run_git_diff_no_index(temp.path(), &origin_dir, &vendor_dir);
        if diff.status > 1 {
            report.errors.push(git_message(&diff));
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        }
        report.changed = !diff.stdout.trim().is_empty();
        report.status = if report.changed {
            "export_ready".to_string()
        } else if origin_summary.file_count == vendor_summary.file_count {
            "no_local_drift".to_string()
        } else {
            "no_textual_diff".to_string()
        };
        if report.changed {
            report.actions.push(AlignmentAction {
                code: "upstream_vendor_patch",
                blocking: false,
                summary: "review and apply the exported patch in the origin dependency repo"
                    .to_string(),
            });
        }

        if options.apply {
            if let Some(dir) = &output_dir {
                let patch_path = dir.join(format!("{}-vendor-vs-origin.patch", spec.name));
                std::fs::write(&patch_path, diff.stdout.as_bytes())
                    .map_err(|source| DepsError::Io { path: patch_path.clone(), source })?;
                report.artifacts.push(patch_path.display().to_string());
                artifacts_written += 1;
            }
        }
        dependencies.push(report);
    }

    let mut report = mutation_report("export", options, dependencies);
    report.summary.artifacts_written = artifacts_written;
    if options.apply {
        if let Some(dir) = &output_dir {
            let manifest = dir.join("manifest.json");
            let rendered = serde_json::to_string_pretty(&report).map_err(DepsError::Json)?;
            std::fs::write(&manifest, rendered)
                .map_err(|source| DepsError::Io { path: manifest.clone(), source })?;
            report.summary.artifacts_written += 1;
        }
    }
    Ok(report)
}

pub fn run_import_transaction(options: &MutationOptions) -> Result<MutationReport, DepsError> {
    let mut lock = load_lock(&options.lock_file)?;
    validate_lock_schema(&lock, &options.lock_file)?;
    let lock_by_name = lock_by_name(lock.owned_dependency.clone());
    let specs = selected_specs(&options.dependencies)?;
    let mut dependencies = Vec::with_capacity(specs.len());
    let mut lock_updates = BTreeMap::new();

    for spec in specs {
        let mut report = base_mutation_dependency_report(spec, &lock_by_name, options);
        if let Err(error) = ensure_live_clone_ready(&report, options.fetch) {
            report.errors.push(error);
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        }
        if let Err(error) = ensure_vendor_target_clean(&options.root, &report.source_path) {
            report.errors.push(error);
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        }

        if !options.allow_overwrite_local_drift {
            report.actions.push(AlignmentAction {
                code: "export_before_import",
                blocking: true,
                summary: "pass --allow-overwrite-local-drift only after exporting/reviewing Trust-local vendor drift".to_string(),
            });
            report.errors.push(
                "import refuses to overwrite the checked-in vendor tree without --allow-overwrite-local-drift".to_string(),
            );
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        }

        let target_path = options.root.join(&report.source_path);
        let target_parent = parent_dir(&target_path)?;
        let source_temp = tempfile::Builder::new()
            .prefix("trust-deps-import-source-")
            .tempdir_in(target_parent)
            .map_err(|source| DepsError::Io { path: target_path.clone(), source })?;
        let staged_source = source_temp.path().join("source");
        let summary = match copy_dependency_origin_tree_with_policy(
            spec,
            Path::new(&report.clone_path),
            &staged_source,
            options.overlay_policy,
        ) {
            Ok(summary) => summary,
            Err(error) => {
                report.errors.push(error);
                report.status = "blocked".to_string();
                dependencies.push(report);
                continue;
            }
        };
        let snapshot = match snapshot_directory(&staged_source) {
            Ok(snapshot) => snapshot,
            Err(error) => {
                report.errors.push(error);
                report.status = "blocked".to_string();
                dependencies.push(report);
                continue;
            }
        };
        report.file_count = summary.file_count;
        report.executable_count = summary.executable_count;
        report.total_bytes = summary.total_bytes;
        report.source_snapshot = Some(snapshot.clone());
        report.changed = true;
        report.status =
            if options.apply { "imported".to_string() } else { "import_ready".to_string() };
        report.actions.push(AlignmentAction {
            code: "replace_vendor_snapshot",
            blocking: false,
            summary: format!(
                "replace {} with tracked files from {}",
                report.source_path, report.clone_path
            ),
        });

        if options.apply {
            if let Err(error) = replace_directory_atomically(&target_path, &staged_source) {
                report.errors.push(error);
                report.status = "blocked".to_string();
                dependencies.push(report);
                continue;
            }
            report.lock_updated = true;
        }

        if let Some(rev) = &report.origin_main {
            lock_updates.insert(spec.name.to_string(), (rev.clone(), snapshot));
        }
        dependencies.push(report);
    }

    let mut lock_updated = false;
    if options.apply && dependencies.iter().all(MutationDependencyReport::ok) {
        apply_lock_updates(&mut lock, &lock_updates);
        let rendered = render_lock_file(&lock)?;
        write_file_atomically(&options.lock_file, rendered.as_bytes()).map_err(DepsError::Git)?;
        lock_updated = true;
    }

    let mut report = mutation_report("import", options, dependencies);
    report.summary.lock_updated = lock_updated;
    Ok(report)
}

pub fn run_lock_transaction(options: &MutationOptions) -> Result<MutationReport, DepsError> {
    let mut lock = load_lock(&options.lock_file)?;
    validate_lock_schema(&lock, &options.lock_file)?;
    let lock_by_name = lock_by_name(lock.owned_dependency.clone());
    let specs = selected_specs(&options.dependencies)?;
    let mut dependencies = Vec::with_capacity(specs.len());
    let mut lock_updates = BTreeMap::new();

    for spec in specs {
        let mut report = base_mutation_dependency_report(spec, &lock_by_name, options);
        if let Err(error) = ensure_live_clone_ready(&report, options.fetch) {
            report.errors.push(error);
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        }
        if let Err(error) = ensure_vendor_target_clean(&options.root, &report.source_path) {
            report.errors.push(error);
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        }
        let Some(rev) = report.origin_main.clone() else {
            report.errors.push("origin/main is unavailable".to_string());
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        };
        let snapshot = match snapshot_git_index(&options.root, &report.source_path) {
            Ok(Some(snapshot)) => snapshot,
            Ok(None) => {
                report
                    .errors
                    .push(format!("{} has no tracked files for lock update", report.source_path));
                report.status = "blocked".to_string();
                dependencies.push(report);
                continue;
            }
            Err(error) => {
                report.errors.push(error);
                report.status = "blocked".to_string();
                dependencies.push(report);
                continue;
            }
        };
        let origin_snapshot = match snapshot_dependency_origin_tree(
            spec,
            Path::new(&report.clone_path),
            options.overlay_policy,
        ) {
            Ok(Some(snapshot)) => snapshot,
            Ok(None) => {
                report.errors.push(format!(
                    "{} has no tracked origin files for lock update",
                    report.clone_path
                ));
                report.status = "blocked".to_string();
                dependencies.push(report);
                continue;
            }
            Err(error) => {
                report.errors.push(error);
                report.status = "blocked".to_string();
                dependencies.push(report);
                continue;
            }
        };
        report.source_snapshot = Some(snapshot.clone());
        if normalize_snapshot(&snapshot) != normalize_snapshot(&origin_snapshot) {
            report.errors.push(format!(
                "checked-in {} snapshot does not match {} origin/main; run export/import before lock update (vendor={}, origin={})",
                report.source_path, report.clone_path, snapshot, origin_snapshot
            ));
            report.actions.push(AlignmentAction {
                code: "import_before_lock",
                blocking: true,
                summary: "lock updates require checked-in vendor content to match origin/main"
                    .to_string(),
            });
            report.status = "blocked".to_string();
            dependencies.push(report);
            continue;
        }
        report.lock_updated = options.apply;
        report.changed = true;
        report.status = if options.apply {
            "lock_updated".to_string()
        } else {
            "lock_update_ready".to_string()
        };
        lock_updates.insert(spec.name.to_string(), (rev, snapshot));
        dependencies.push(report);
    }

    let mut lock_updated = false;
    if options.apply && dependencies.iter().all(MutationDependencyReport::ok) {
        apply_lock_updates(&mut lock, &lock_updates);
        let rendered = render_lock_file(&lock)?;
        write_file_atomically(&options.lock_file, rendered.as_bytes()).map_err(DepsError::Git)?;
        lock_updated = true;
    }

    let mut report = mutation_report("lock", options, dependencies);
    report.summary.lock_updated = lock_updated;
    Ok(report)
}

pub fn render_mutation_json(report: &MutationReport) -> Result<String, DepsError> {
    serde_json::to_string_pretty(report).map_err(DepsError::Json)
}

pub fn render_mutation_text(report: &MutationReport) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "targo trust deps {}: {} ok, {} failed, {} total",
        report.command, report.summary.ok, report.summary.failed, report.summary.total
    );
    let _ = writeln!(
        out,
        "changed={} artifacts_written={} lock_updated={} overlay_policy={}",
        report.summary.changed,
        report.summary.artifacts_written,
        report.summary.lock_updated,
        report.overlay_policy.as_str()
    );
    for dependency in &report.dependencies {
        let _ = writeln!(
            out,
            "\n{} ({}) - {}",
            dependency.display_name, dependency.name, dependency.status
        );
        let _ = writeln!(out, "  source: {}", dependency.source_path);
        let _ = writeln!(out, "  clone: {}", dependency.clone_path);
        let _ = writeln!(
            out,
            "  origin_main: {}",
            dependency.origin_main.as_deref().unwrap_or("<missing>")
        );
        if let Some(snapshot) = &dependency.source_snapshot {
            let _ = writeln!(out, "  source_snapshot: {snapshot}");
        }
        let _ = writeln!(
            out,
            "  files={} executables={} bytes={}",
            dependency.file_count, dependency.executable_count, dependency.total_bytes
        );
        for artifact in &dependency.artifacts {
            let _ = writeln!(out, "  artifact: {artifact}");
        }
        for error in &dependency.errors {
            let _ = writeln!(out, "  error: {error}");
        }
        for action in &dependency.actions {
            let _ = writeln!(out, "  action: {} - {}", action.code, action.summary);
        }
    }
    out
}

pub fn render_diff_text(report: &AlignmentReport) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "Trust dependency drift classification");
    for dependency in &report.dependencies {
        let snapshot_blocks = dependency.source_snapshot_status.is_blocking();
        let class = if snapshot_blocks && !dependency.lock_current {
            "vendor_snapshot_and_lock_drift"
        } else if snapshot_blocks {
            "vendor_snapshot_drift"
        } else if !dependency.lock_current {
            "origin_only"
        } else if dependency.live_clone_status != LiveCloneStatus::Aligned {
            "live_clone_drift"
        } else {
            "aligned"
        };
        let _ = writeln!(
            out,
            "- {}: {} (lock={}, origin={}, snapshot={:?}, live={:?})",
            dependency.display_name,
            class,
            dependency.lock_rev.as_deref().unwrap_or("<missing>"),
            dependency.origin_main.as_deref().unwrap_or("<missing>"),
            dependency.source_snapshot_status,
            dependency.live_clone_status,
        );
    }
    out
}

pub fn render_upstream_plan_text(report: &AlignmentReport) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "Trust dependency upstream/import plan");
    for dependency in &report.dependencies {
        let _ = writeln!(out, "\n{}", dependency.display_name);
        if dependency.live_clone_status != LiveCloneStatus::Aligned {
            let _ = writeln!(
                out,
                "  1. Fix live clone state first: {:?}",
                dependency.live_clone_status
            );
        } else if matches!(
            dependency.source_snapshot_status,
            SnapshotStatus::Mismatch | SnapshotStatus::Missing | SnapshotStatus::Error
        ) {
            let _ = writeln!(
                out,
                "  1. Audit Trust vendored snapshot changes against {} origin/main.",
                dependency.display_name
            );
            let _ = writeln!(
                out,
                "  2. Upstream dependency-owned changes or discard Trust-local baggage."
            );
            let _ = writeln!(
                out,
                "  3. Re-import a deterministic snapshot from origin/main and update trust-engines.lock."
            );
        } else if dependency.source_snapshot_status == SnapshotStatus::Unchecked {
            let _ = writeln!(
                out,
                "  1. Run `targo trust deps status --deep-hash --json` before changing lock hashes."
            );
            let _ = writeln!(
                out,
                "  2. Use the fast fingerprint only for triage, not release admission."
            );
        } else if !dependency.lock_current {
            let _ = writeln!(
                out,
                "  1. Import origin/main {} into {}.",
                dependency.origin_main.as_deref().unwrap_or("<missing>"),
                dependency.source_path
            );
            let _ =
                writeln!(out, "  2. Update trust-engines.lock rev and source_snapshot together.");
        } else {
            let _ = writeln!(out, "  aligned; no upstream/import action required.");
        }

        for action in &dependency.actions {
            let _ = writeln!(
                out,
                "  action[{} blocking={}]: {}",
                action.code, action.blocking, action.summary
            );
        }
    }
    out
}

fn load_lock(path: &Path) -> Result<LockFile, DepsError> {
    let text = std::fs::read_to_string(path)
        .map_err(|source| DepsError::Io { path: path.to_path_buf(), source })?;
    toml::from_str(&text).map_err(|source| DepsError::Toml { path: path.to_path_buf(), source })
}

fn validate_lock_schema(lock: &LockFile, path: &Path) -> Result<(), DepsError> {
    if lock.schema != LOCK_SCHEMA {
        return Err(DepsError::InvalidLock(format!(
            "{} schema is {:?}, expected {LOCK_SCHEMA:?}",
            path.display(),
            lock.schema
        )));
    }
    Ok(())
}

fn lock_by_name(entries: Vec<OwnedDependency>) -> BTreeMap<String, OwnedDependency> {
    entries.into_iter().map(|dependency| (dependency.name.clone(), dependency)).collect()
}

fn selected_specs(names: &[String]) -> Result<Vec<&'static DependencySpec>, DepsError> {
    if names.is_empty() {
        return Ok(DEPENDENCIES.iter().collect());
    }
    let mut selected = Vec::with_capacity(names.len());
    for name in names {
        let normalized = name.to_ascii_lowercase();
        let Some(spec) = DEPENDENCIES.iter().find(|spec| spec.name == normalized) else {
            return Err(DepsError::InvalidLock(format!("unknown Trust-owned dependency `{name}`")));
        };
        if selected.iter().any(|existing: &&DependencySpec| existing.name == spec.name) {
            continue;
        }
        selected.push(spec);
    }
    Ok(selected)
}

fn mutation_report(
    command: &'static str,
    options: &MutationOptions,
    dependencies: Vec<MutationDependencyReport>,
) -> MutationReport {
    let mut summary = MutationSummary { total: dependencies.len(), ..MutationSummary::default() };
    for dependency in &dependencies {
        if dependency.ok() {
            summary.ok += 1;
        } else {
            summary.failed += 1;
        }
        if dependency.changed {
            summary.changed += 1;
        }
    }
    MutationReport {
        schema: "trust.deps.mutation.v1",
        command: command.to_string(),
        apply_requested: options.apply,
        overlay_policy: options.overlay_policy,
        root: options.root.display().to_string(),
        lock_file: options.lock_file.display().to_string(),
        output_dir: options.output_dir.as_ref().map(|path| path.display().to_string()),
        summary,
        dependencies,
    }
}

fn base_mutation_dependency_report(
    spec: &DependencySpec,
    lock_by_name: &BTreeMap<String, OwnedDependency>,
    options: &MutationOptions,
) -> MutationDependencyReport {
    let lock_entry = lock_by_name.get(spec.name);
    let source_path =
        lock_entry.map(|entry| entry.path.clone()).unwrap_or_else(|| spec.source_path.to_string());
    let clone_path = clone_path_for(spec, &options.clone_root);
    let clone_head =
        if clone_path.exists() { git_stdout(&clone_path, &["rev-parse", "HEAD"]) } else { None };
    let origin_main = if clone_path.exists() {
        git_stdout(&clone_path, &["rev-parse", "--verify", "refs/remotes/origin/main^{commit}"])
    } else {
        None
    };

    MutationDependencyReport {
        name: spec.name.to_string(),
        display_name: lock_entry
            .map(|entry| entry.display_name.clone())
            .unwrap_or_else(|| spec.display_name.to_string()),
        source_path,
        clone_path: clone_path.display().to_string(),
        clone_head,
        origin_main,
        status: "planned".to_string(),
        changed: false,
        file_count: 0,
        executable_count: 0,
        total_bytes: 0,
        source_snapshot: None,
        lock_updated: false,
        artifacts: Vec::new(),
        errors: Vec::new(),
        actions: Vec::new(),
    }
}

fn ensure_live_clone_ready(report: &MutationDependencyReport, fetch: bool) -> Result<(), String> {
    let clone_path = Path::new(&report.clone_path);
    if !clone_path.exists() {
        return Err(format!("dependency clone does not exist: {}", report.clone_path));
    }
    if !is_git_worktree(clone_path) {
        return Err(format!("dependency clone is not a git worktree: {}", report.clone_path));
    }
    if fetch {
        let fetch = run_git(
            clone_path,
            &["fetch", "--quiet", "origin", "+refs/heads/main:refs/remotes/origin/main"],
        );
        if fetch.status != 0 {
            return Err(format!(
                "failed to fetch origin/main in {}: {}",
                report.clone_path,
                git_message(&fetch)
            ));
        }
    }
    let dirty =
        git_stdout(clone_path, &["status", "--porcelain"]).is_none_or(|status| !status.is_empty());
    if dirty {
        return Err(format!("dependency clone is dirty: {}", report.clone_path));
    }
    let head = git_stdout(clone_path, &["rev-parse", "HEAD"])
        .ok_or_else(|| format!("dependency clone has no HEAD: {}", report.clone_path))?;
    let origin =
        git_stdout(clone_path, &["rev-parse", "--verify", "refs/remotes/origin/main^{commit}"])
            .ok_or_else(|| format!("dependency clone has no origin/main: {}", report.clone_path))?;
    if head != origin {
        return Err(format!(
            "dependency clone is not fast-forwarded to origin/main: {} HEAD={} origin/main={}",
            report.clone_path, head, origin
        ));
    }
    Ok(())
}

fn ensure_vendor_target_clean(root: &Path, source_path: &str) -> Result<(), String> {
    let path = root.join(source_path);
    if path.exists() && !path.is_dir() {
        return Err(format!("{source_path} is not a directory"));
    }
    if path.is_symlink() {
        return Err(format!("{source_path} must not be a symlink"));
    }
    if source_path_is_dirty(root, source_path)? {
        return Err(format!(
            "{source_path} has local git changes; commit or stash before dependency mutation"
        ));
    }
    Ok(())
}

fn source_path_is_dirty(root: &Path, source_path: &str) -> Result<bool, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["status", "--porcelain", "--", source_path])
        .output()
        .map_err(|error| format!("git status failed for {source_path}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "git status failed for {source_path}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(!output.stdout.is_empty())
}

#[derive(Debug, Clone, Default)]
struct CopySummary {
    file_count: usize,
    executable_count: usize,
    total_bytes: u64,
}

#[derive(Debug, Clone)]
struct GitIndexEntry {
    mode: String,
    blob: String,
    repo_path: String,
}

fn copy_git_tracked_tree(
    repo: &Path,
    pathspec: Option<&str>,
    destination: &Path,
) -> Result<CopySummary, String> {
    std::fs::create_dir_all(destination)
        .map_err(|error| format!("failed to create {}: {error}", destination.display()))?;
    let entries = git_index_entries(repo, pathspec)?;
    let by_path: BTreeMap<String, GitIndexEntry> =
        entries.iter().map(|entry| (entry.repo_path.clone(), entry.clone())).collect();
    let mut summary = CopySummary::default();
    let mut blob_reader = GitBlobReader::new(repo)?;
    for entry in &entries {
        if entry.mode == "120000" {
            copy_materialized_symlink(
                repo,
                &mut blob_reader,
                &entries,
                &by_path,
                entry,
                pathspec,
                destination,
                &mut summary,
            )?;
            continue;
        }
        if entry.mode != "100644" && entry.mode != "100755" {
            return Err(format!(
                "unsupported git file mode {} for {}",
                entry.mode, entry.repo_path
            ));
        }
        let relative = output_relative_path(&entry.repo_path, pathspec);
        write_git_blob(
            &mut blob_reader,
            destination,
            &relative,
            &entry.mode,
            &entry.blob,
            &mut summary,
        )?;
    }
    Ok(summary)
}

#[cfg(test)]
fn copy_dependency_origin_tree(
    spec: &DependencySpec,
    repo: &Path,
    destination: &Path,
) -> Result<CopySummary, String> {
    copy_dependency_origin_tree_with_policy(spec, repo, destination, OverlayPolicy::Forbid)
}

fn copy_dependency_origin_tree_with_policy(
    spec: &DependencySpec,
    repo: &Path,
    destination: &Path,
    overlay_policy: OverlayPolicy,
) -> Result<CopySummary, String> {
    copy_git_tracked_tree(repo, None, destination)?;
    let overlay_actions = dependency_snapshot_overlay_actions(spec);
    if !overlay_actions.is_empty() {
        if overlay_policy == OverlayPolicy::Forbid {
            return Err(format!(
                "{} requires dependency snapshot overlays: {}; rerun with \
                 --overlay-policy bootstrap only after confirming those overlays are \
                 committed in the standalone dependency repo and needed for bootstrap",
                spec.name,
                overlay_actions.join(", ")
            ));
        }
        apply_dependency_snapshot_overlays(spec, destination)?;
    }
    require_no_owned_cargo_git_sources(destination)?;
    summarize_snapshot_directory(destination)
}

fn dependency_snapshot_overlay_actions(spec: &DependencySpec) -> Vec<&'static str> {
    match spec.name {
        "trust-cg" => vec!["apply upstream dependency-modes/trust Cargo overlay"],
        "trust-wp" => vec!["apply upstream dependency-modes/trust root manifest and lock overlay"],
        "trust-mc" => vec!["apply upstream dependency-modes/trust manifest and lock overlay"],
        "ty" => vec!["apply upstream dependency-modes/trust contract"],
        "ay" => vec!["apply upstream dependency-modes/trust Cargo overlay"],
        _ => Vec::new(),
    }
}

fn apply_dependency_snapshot_overlays(spec: &DependencySpec, root: &Path) -> Result<(), String> {
    match spec.name {
        "trust-vc" => Ok(()),
        "trust-wp" => apply_trust_wp_dependency_mode_overlay(root),
        "trust-cg" | "trust-mc" => apply_dependency_mode_directory_overlay(root),
        "ty" => apply_ty_dependency_mode_overlay(root),
        "ay" => apply_ay_snapshot_overlay(root),
        _ => Ok(()),
    }
}

fn apply_trust_wp_dependency_mode_overlay(root: &Path) -> Result<(), String> {
    copy_dependency_mode_file(root, Path::new("dependency-modes/trust/Cargo.toml"), "Cargo.toml")?;
    copy_dependency_mode_file(root, Path::new("dependency-modes/trust/Cargo.lock"), "Cargo.lock")?;
    Ok(())
}

fn apply_dependency_mode_directory_overlay(root: &Path) -> Result<(), String> {
    let source = root.join("dependency-modes/trust");
    if !source.is_dir() {
        return Err(format!("missing dependency mode overlay directory: {}", source.display()));
    }
    copy_filesystem_tree(&source, root)
}

fn apply_ty_dependency_mode_overlay(root: &Path) -> Result<(), String> {
    let directory = root.join("dependency-modes/trust");
    if directory.is_dir() {
        return copy_filesystem_tree(&directory, root);
    }
    let contract_path = root.join("dependency-modes/trust.toml");
    let text = std::fs::read_to_string(&contract_path)
        .map_err(|error| format!("failed to read {}: {error}", contract_path.display()))?;
    let contract: TyTrustModeContract = toml::from_str(&text)
        .map_err(|error| format!("failed to parse {}: {error}", contract_path.display()))?;
    let (package_paths, markers) = ty_trust_package_paths_and_markers(&contract);
    rewrite_ty_trust_manifest(&root.join("Cargo.toml"), &package_paths)?;
    let marker_refs: Vec<&str> = markers.iter().map(String::as_str).collect();
    strip_cargo_lock_git_sources_under(root, &marker_refs)
}

fn copy_dependency_mode_file(
    root: &Path,
    source_relative: &Path,
    destination_relative: &str,
) -> Result<(), String> {
    let source = root.join(source_relative);
    let destination = root.join(destination_relative);
    copy_single_file_preserving_permissions(&source, &destination)
}

fn copy_single_file_preserving_permissions(
    source: &Path,
    destination: &Path,
) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(source)
        .map_err(|error| format!("failed to stat {}: {error}", source.display()))?;
    if metadata.file_type().is_symlink() {
        return Err(format!("refusing to copy symlink {}", source.display()));
    }
    if !metadata.is_file() {
        return Err(format!("{} is not a file", source.display()));
    }
    if let Some(parent) = destination.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|error| format!("failed to create {}: {error}", parent.display()))?;
    }
    std::fs::copy(source, destination)
        .map_err(|error| format!("failed to copy {}: {error}", source.display()))?;
    std::fs::set_permissions(destination, metadata.permissions()).map_err(|error| {
        format!("failed to set permissions on {}: {error}", destination.display())
    })?;
    Ok(())
}

fn apply_ay_snapshot_overlay(root: &Path) -> Result<(), String> {
    if ay_dependency_mode_assets_present(root) {
        return apply_dependency_mode_assets_overlay(root);
    }
    apply_ay_bootstrap_snapshot_overlay(root)
}

fn ay_dependency_mode_assets_present(root: &Path) -> bool {
    ["Cargo.toml", "Cargo.lock", "crates/ay-jit/Cargo.toml"]
        .into_iter()
        .all(|relative| root.join("dependency-modes/trust").join(relative).is_file())
}

fn apply_dependency_mode_assets_overlay(root: &Path) -> Result<(), String> {
    let directory = root.join("dependency-modes/trust");
    if directory.is_dir() {
        return copy_filesystem_tree(&directory, root);
    }
    Err(format!("missing dependency mode overlay directory: {}", directory.display()))
}

fn apply_ay_bootstrap_snapshot_overlay(root: &Path) -> Result<(), String> {
    rewrite_manifest_dependency_lines(
        &root.join("Cargo.toml"),
        &[
            (
                "trust-ir =",
                r#"trust-ir = { version = "0.1.0", path = "../trust-ir/crates/trust-ir", features = ["serde", "parser"] }"#,
            ),
            (
                "trust-ir-build =",
                r#"trust-ir-build = { path = "../trust-ir/crates/trust-ir-build" }"#,
            ),
        ],
    )?;
    rewrite_manifest_dependency_lines(
        &root.join("crates/ay-jit/Cargo.toml"),
        &[(
            "trust-cg-codegen =",
            r#"trust-cg-codegen = { version = "0.1.0", path = "../../../trust-codegen/crates/trust-cg-codegen", default-features = false, optional = true }"#,
        )],
    )?;
    strip_cargo_lock_git_sources_under(
        root,
        &[
            "alabsystems/trust-cg",
            "alabsystems/TrustIr",
            "alabsystems/trust-codegen",
            "alabsystems/trust_ir",
            "alabsystems/trust-ir",
        ],
    )?;
    Ok(())
}

#[derive(Debug, serde::Deserialize)]
struct TyTrustModeContract {
    trust: TyTrustMode,
}

#[derive(Debug, serde::Deserialize)]
struct TyTrustMode {
    replacements: Vec<TyTrustReplacement>,
}

#[derive(Debug, serde::Deserialize)]
struct TyTrustReplacement {
    source: Option<String>,
    patched_source: Option<String>,
    default_relative_path: String,
    packages: Vec<String>,
}

fn ty_trust_package_paths_and_markers(
    contract: &TyTrustModeContract,
) -> (BTreeMap<String, String>, Vec<String>) {
    let mut package_paths = BTreeMap::new();
    let mut markers = BTreeSet::new();
    for replacement in &contract.trust.replacements {
        let relative_root = replacement.default_relative_path.trim_end_matches('/');
        for package in &replacement.packages {
            package_paths.insert(package.clone(), format!("{relative_root}/crates/{package}"));
        }
        for source in [&replacement.source, &replacement.patched_source].into_iter().flatten() {
            if let Some(marker) = owned_git_marker(source) {
                markers.insert(marker);
            }
        }
    }
    (package_paths, markers.into_iter().collect())
}

fn owned_git_marker(source: &str) -> Option<String> {
    let source = source.strip_prefix("git+").unwrap_or(source);
    let marker = if let Some((_, rest)) = source.split_once("github.com/") {
        rest
    } else if let Some((_, rest)) = source.split_once("github.com:") {
        rest
    } else {
        return None;
    };
    let marker = marker.split(['?', '#']).next().unwrap_or(marker).trim_end_matches(".git");
    if marker.is_empty() { None } else { Some(marker.to_string()) }
}

fn rewrite_ty_trust_manifest(
    path: &Path,
    package_paths: &BTreeMap<String, String>,
) -> Result<(), String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
    let mut rendered = String::new();
    let mut seen = BTreeSet::new();
    for line in text.lines() {
        let trimmed = line.trim_start();
        let mut replacement = None;
        for (package, local_path) in package_paths {
            if trimmed.starts_with(&format!("{package} =")) {
                if let Some(spec) = parse_manifest_dependency_line(line, package)? {
                    if spec.get("git").is_some() {
                        seen.insert(package.clone());
                        replacement =
                            Some(render_path_dependency_line(package, local_path, &spec)?);
                    }
                }
                break;
            }
        }
        rendered.push_str(replacement.as_deref().unwrap_or(line));
        rendered.push('\n');
    }
    let missing: Vec<_> =
        package_paths.keys().filter(|package| !seen.contains(*package)).cloned().collect();
    if !missing.is_empty() {
        return Err(format!(
            "{} is missing Trust-mode git dependency lines: {}",
            path.display(),
            missing.join(", ")
        ));
    }
    if rendered != text {
        std::fs::write(path, rendered)
            .map_err(|error| format!("failed to write {}: {error}", path.display()))?;
    }
    Ok(())
}

fn parse_manifest_dependency_line(
    line: &str,
    package: &str,
) -> Result<Option<toml::Table>, String> {
    let value: toml::Value = toml::from_str(line)
        .map_err(|error| format!("failed to parse dependency line: {error}"))?;
    Ok(value
        .as_table()
        .and_then(|table| table.get(package))
        .and_then(toml::Value::as_table)
        .cloned())
}

fn render_path_dependency_line(
    package: &str,
    path: &str,
    spec: &toml::Table,
) -> Result<String, String> {
    let mut entries = Vec::new();
    entries.push(("path", toml::Value::String(path.to_string())));
    for key in ["package", "default-features", "features", "optional"] {
        if let Some(value) = spec.get(key) {
            entries.push((key, value.clone()));
        }
    }
    let fields = entries
        .into_iter()
        .map(|(key, value)| {
            format_inline_toml_value(&value).map(|rendered| format!("{key} = {rendered}"))
        })
        .collect::<Result<Vec<_>, String>>()?
        .join(", ");
    Ok(format!("{package} = {{ {fields} }}"))
}

fn format_inline_toml_value(value: &toml::Value) -> Result<String, String> {
    match value {
        toml::Value::Boolean(value) => Ok(value.to_string()),
        toml::Value::String(value) => Ok(format!("{value:?}")),
        toml::Value::Array(values) => {
            let rendered = values
                .iter()
                .map(format_inline_toml_value)
                .collect::<Result<Vec<_>, String>>()?
                .join(", ");
            Ok(format!("[{rendered}]"))
        }
        other => Err(format!("unsupported dependency inline value: {other:?}")),
    }
}

fn rewrite_manifest_dependency_lines(
    path: &Path,
    replacements: &[(&str, &str)],
) -> Result<(), String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
    let mut seen = vec![false; replacements.len()];
    let mut rendered = String::new();
    for line in text.lines() {
        let trimmed = line.trim_start();
        let mut replacement = None;
        for (index, (prefix, new_line)) in replacements.iter().enumerate() {
            if trimmed.starts_with(prefix) {
                seen[index] = true;
                replacement = Some(*new_line);
                break;
            }
        }
        rendered.push_str(replacement.unwrap_or(line));
        rendered.push('\n');
    }
    let missing: Vec<&str> = replacements
        .iter()
        .zip(seen.iter())
        .filter_map(|((prefix, _), found)| (!found).then_some(*prefix))
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "{} is missing dependency lines required for Trust overlay: {}",
            path.display(),
            missing.join(", ")
        ));
    }
    if rendered != text {
        std::fs::write(path, rendered)
            .map_err(|error| format!("failed to write {}: {error}", path.display()))?;
    }
    Ok(())
}

fn strip_cargo_lock_git_sources(path: &Path, markers: &[&str]) -> Result<(), String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
    let mut rendered = String::new();
    for line in text.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("source = \"git+")
            && markers.iter().any(|marker| trimmed.contains(marker))
        {
            continue;
        }
        let stripped = strip_lock_dependency_git_suffixes(line, markers);
        rendered.push_str(&stripped);
        rendered.push('\n');
    }
    if rendered != text {
        std::fs::write(path, rendered)
            .map_err(|error| format!("failed to write {}: {error}", path.display()))?;
    }
    Ok(())
}

fn strip_cargo_lock_git_sources_under(root: &Path, markers: &[&str]) -> Result<(), String> {
    let mut lockfiles = Vec::new();
    collect_cargo_lock_files(root, Path::new(""), &mut lockfiles)?;
    for lockfile in lockfiles {
        strip_cargo_lock_git_sources(&lockfile, markers)?;
    }
    Ok(())
}

fn collect_cargo_lock_files(
    root: &Path,
    relative: &Path,
    lockfiles: &mut Vec<PathBuf>,
) -> Result<(), String> {
    let directory = root.join(relative);
    let mut entries = Vec::new();
    for entry in std::fs::read_dir(&directory)
        .map_err(|error| format!("failed to read {}: {error}", directory.display()))?
    {
        entries.push(entry.map_err(|error| {
            format!("failed to read entry under {}: {error}", directory.display())
        })?);
    }
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let child_relative = relative.join(entry.file_name());
        let child_posix = child_relative.to_string_lossy().replace('\\', "/");
        if is_dependency_snapshot_excluded_relative_path(&child_posix) {
            continue;
        }
        let file_type = entry.file_type().map_err(|error| {
            format!("failed to read file type for {}: {error}", entry.path().display())
        })?;
        if file_type.is_dir() {
            collect_cargo_lock_files(root, &child_relative, lockfiles)?;
        } else if file_type.is_file() && entry.file_name() == "Cargo.lock" {
            lockfiles.push(entry.path());
        }
    }
    Ok(())
}

fn strip_lock_dependency_git_suffixes(line: &str, markers: &[&str]) -> String {
    let mut rendered = line.to_string();
    while let Some(start) = rendered.find(" (git+") {
        let search_from = start + 1;
        let Some(end_relative) = rendered[search_from..].find(')') else {
            break;
        };
        let end = search_from + end_relative + 1;
        let suffix = &rendered[start..end];
        if markers.iter().any(|marker| suffix.contains(marker)) {
            rendered.replace_range(start..end, "");
        } else {
            break;
        }
    }
    rendered
}

fn require_no_owned_cargo_git_sources(root: &Path) -> Result<(), String> {
    let manifests = collect_files_named(root, "Cargo.toml")?;
    for path in manifests {
        let text = std::fs::read_to_string(&path)
            .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
        for (index, line) in text.lines().enumerate() {
            if line.contains("git")
                && (line.contains("git =") || line.contains("git="))
                && contains_owned_github_repo_identity(line)
            {
                let relative = display_relative_path(root, &path);
                return Err(format!(
                    "{relative}:{}: owned snapshot Cargo manifest must not contain owned git dependency source {:?}",
                    index + 1,
                    line.trim()
                ));
            }
        }
    }

    let lockfiles = collect_files_named(root, "Cargo.lock")?;
    for path in lockfiles {
        let text = std::fs::read_to_string(&path)
            .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
        for (index, line) in text.lines().enumerate() {
            if line.contains("git+") && contains_owned_github_repo_identity(line) {
                let relative = display_relative_path(root, &path);
                return Err(format!(
                    "{relative}:{}: owned snapshot Cargo.lock must not contain owned git source identity {:?}",
                    index + 1,
                    line.trim()
                ));
            }
        }
    }

    Ok(())
}

fn collect_files_named(root: &Path, file_name: &str) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    collect_files_named_inner(root, Path::new(""), file_name, &mut files)?;
    Ok(files)
}

fn collect_files_named_inner(
    root: &Path,
    relative: &Path,
    file_name: &str,
    files: &mut Vec<PathBuf>,
) -> Result<(), String> {
    let directory = root.join(relative);
    let mut entries = Vec::new();
    for entry in std::fs::read_dir(&directory)
        .map_err(|error| format!("failed to read {}: {error}", directory.display()))?
    {
        entries.push(entry.map_err(|error| {
            format!("failed to read entry under {}: {error}", directory.display())
        })?);
    }
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let child_relative = relative.join(entry.file_name());
        let child_posix = child_relative.to_string_lossy().replace('\\', "/");
        if is_dependency_snapshot_excluded_relative_path(&child_posix) {
            continue;
        }
        let file_type = entry.file_type().map_err(|error| {
            format!("failed to read file type for {}: {error}", entry.path().display())
        })?;
        if file_type.is_dir() {
            collect_files_named_inner(root, &child_relative, file_name, files)?;
        } else if file_type.is_file() && entry.file_name() == file_name {
            files.push(entry.path());
        }
    }
    Ok(())
}

fn display_relative_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root).unwrap_or(path).to_string_lossy().replace('\\', "/")
}

fn contains_owned_github_repo_identity(line: &str) -> bool {
    let lower = line.to_ascii_lowercase();
    let mut search_start = 0;
    while let Some(offset) = lower[search_start..].find("github.com") {
        let mut rest = &lower[search_start + offset + "github.com".len()..];
        if let Some(after_colon) = rest.strip_prefix(':') {
            let next_separator = after_colon.find(['/', ':']).unwrap_or(after_colon.len());
            let first_segment = &after_colon[..next_separator];
            if !first_segment.is_empty()
                && first_segment.chars().all(|character| character.is_ascii_digit())
                && after_colon[next_separator..].starts_with('/')
            {
                rest = &after_colon[next_separator + 1..];
            } else {
                rest = after_colon;
            }
        } else if let Some(after_slash) = rest.strip_prefix('/') {
            rest = after_slash;
        } else {
            search_start += offset + "github.com".len();
            continue;
        }

        let Some((org, after_org)) = rest.split_once('/') else {
            search_start += offset + "github.com".len();
            continue;
        };
        let repo = after_org
            .split(['/', '?', '#', '"', '\'', ')', ']', '}', ','])
            .next()
            .unwrap_or("")
            .trim_end_matches(".git");
        if OWNED_GITHUB_ORGS.contains(&org) && OWNED_GITHUB_REPOS.contains(&repo) {
            return true;
        }
        search_start += offset + "github.com".len();
    }
    false
}

fn summarize_snapshot_directory(path: &Path) -> Result<CopySummary, String> {
    let mut files = Vec::new();
    let mut directories = BTreeSet::new();
    collect_directory_entries(path, Path::new(""), &mut directories, &mut files)?;
    Ok(CopySummary {
        file_count: files.len(),
        executable_count: files.iter().filter(|(_, executable, _)| *executable).count(),
        total_bytes: files.iter().map(|(_, _, len)| *len).sum(),
    })
}

fn should_include_dependency_snapshot_path(repo_path: &str, pathspec: Option<&str>) -> bool {
    let relative = output_relative_path(repo_path, pathspec);
    !is_dependency_snapshot_excluded_relative_path(&relative)
}

fn is_dependency_snapshot_excluded_relative_path(relative: &str) -> bool {
    let relative = relative.trim_start_matches("./");
    if relative.is_empty() {
        return false;
    }
    SNAPSHOT_EXCLUDED_ROOT_FILES.contains(&relative)
        || is_dependency_snapshot_runtime_root_file(relative)
        || Path::new(relative)
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| SNAPSHOT_EXCLUDED_FILE_NAMES.contains(&name))
        || SNAPSHOT_EXCLUDED_FILE_SUFFIXES.iter().any(|suffix| relative.ends_with(*suffix))
        || SNAPSHOT_EXCLUDED_PREFIXES
            .iter()
            .any(|prefix| relative == prefix.trim_end_matches('/') || relative.starts_with(prefix))
        || has_dependency_snapshot_excluded_component(relative)
}

fn is_dependency_snapshot_runtime_root_file(relative: &str) -> bool {
    !relative.contains('/')
        && (relative.starts_with(".manager_")
            || relative.starts_with(".worker_")
            || relative.starts_with(".pid_"))
}

fn has_dependency_snapshot_excluded_component(relative: &str) -> bool {
    Path::new(relative).components().any(|component| {
        let std::path::Component::Normal(name) = component else {
            return false;
        };
        let Some(name) = name.to_str() else {
            return false;
        };
        SNAPSHOT_EXCLUDED_PATH_COMPONENTS.contains(&name)
    })
}

fn git_index_entries(repo: &Path, pathspec: Option<&str>) -> Result<Vec<GitIndexEntry>, String> {
    let mut args = vec!["ls-files", "--stage", "-z"];
    let owned_pathspec;
    if let Some(pathspec) = pathspec {
        owned_pathspec = pathspec.to_string();
        args.push("--");
        args.push(&owned_pathspec);
    }
    let listing = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(&args)
        .output()
        .map_err(|error| format!("git ls-files failed in {}: {error}", repo.display()))?;
    if !listing.status.success() {
        return Err(format!(
            "git ls-files failed in {}: {}",
            repo.display(),
            String::from_utf8_lossy(&listing.stderr).trim()
        ));
    }
    let mut entries = Vec::new();
    for record in listing.stdout.split(|byte| *byte == 0).filter(|record| !record.is_empty()) {
        let Some(tab) = record.iter().position(|byte| *byte == b'\t') else {
            return Err(format!("malformed git index record in {}", repo.display()));
        };
        let meta = String::from_utf8_lossy(&record[..tab]);
        let path = String::from_utf8_lossy(&record[tab + 1..]).to_string();
        let mut parts = meta.split_whitespace();
        let mode = parts.next().unwrap_or_default().to_string();
        let blob = parts.next().unwrap_or_default().to_string();
        if blob.is_empty() {
            return Err(format!("malformed git index object in {}", repo.display()));
        }
        if should_include_dependency_snapshot_path(&path, pathspec) {
            entries.push(GitIndexEntry { mode, blob, repo_path: path });
        }
    }
    Ok(entries)
}

#[allow(clippy::too_many_arguments)] // symlink materialization needs both source-side git state and destination state
fn copy_materialized_symlink(
    repo: &Path,
    blob_reader: &mut GitBlobReader,
    entries: &[GitIndexEntry],
    by_path: &BTreeMap<String, GitIndexEntry>,
    link: &GitIndexEntry,
    pathspec: Option<&str>,
    destination: &Path,
    summary: &mut CopySummary,
) -> Result<(), String> {
    let target_bytes = blob_reader.read_blob(&link.blob)?;
    let target_text = String::from_utf8(target_bytes).map_err(|error| {
        format!(
            "symlink target for {} is not valid UTF-8 in {}: {error}",
            link.repo_path,
            repo.display()
        )
    })?;
    let Some(target_repo_path) = resolve_repo_symlink_target(&link.repo_path, &target_text) else {
        return Err(format!(
            "symlinks must stay inside dependency repositories: {} -> {}",
            link.repo_path, target_text
        ));
    };

    let link_relative = output_relative_path(&link.repo_path, pathspec);
    if let Some(target) = by_path.get(&target_repo_path) {
        if target.mode == "120000" {
            return Err(format!(
                "nested symlink materialization is not supported: {} -> {}",
                link.repo_path, target_repo_path
            ));
        }
        write_git_blob(
            blob_reader,
            destination,
            &link_relative,
            &target.mode,
            &target.blob,
            summary,
        )?;
        return Ok(());
    }

    let prefix = format!("{target_repo_path}/");
    let mut materialized = 0usize;
    for target in entries.iter().filter(|entry| entry.repo_path.starts_with(&prefix)) {
        if target.mode == "120000" {
            return Err(format!(
                "nested symlink materialization is not supported under {}: {}",
                link.repo_path, target.repo_path
            ));
        }
        let suffix = target.repo_path.strip_prefix(&prefix).unwrap_or(target.repo_path.as_str());
        let relative = if suffix.is_empty() {
            link_relative.clone()
        } else {
            format!("{link_relative}/{suffix}")
        };
        write_git_blob(blob_reader, destination, &relative, &target.mode, &target.blob, summary)?;
        materialized += 1;
    }
    if materialized == 0 {
        return Err(format!(
            "symlink target is not tracked in {}: {} -> {}",
            repo.display(),
            link.repo_path,
            target_text
        ));
    }
    Ok(())
}

fn write_git_blob(
    blob_reader: &mut GitBlobReader,
    destination: &Path,
    relative: &str,
    mode: &str,
    blob: &str,
    summary: &mut CopySummary,
) -> Result<(), String> {
    let content = blob_reader.read_blob(blob)?;
    let target = destination.join(relative);
    if let Some(parent) = target.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|error| format!("failed to create {}: {error}", parent.display()))?;
    }
    std::fs::write(&target, &content)
        .map_err(|error| format!("failed to write {}: {error}", target.display()))?;
    if mode == "100755" {
        set_executable(&target)?;
        summary.executable_count += 1;
    }
    summary.file_count += 1;
    summary.total_bytes += content.len() as u64;
    Ok(())
}

fn output_relative_path(repo_path: &str, pathspec: Option<&str>) -> String {
    match pathspec {
        Some(prefix) if repo_path == prefix => Path::new(repo_path)
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or(repo_path)
            .to_string(),
        Some(prefix) => {
            repo_path.strip_prefix(&format!("{prefix}/")).unwrap_or(repo_path).to_string()
        }
        None => repo_path.to_string(),
    }
}

fn resolve_repo_symlink_target(link_repo_path: &str, target: &str) -> Option<String> {
    let target_path = Path::new(target);
    if target_path.is_absolute() {
        return None;
    }
    let parent = Path::new(link_repo_path).parent().unwrap_or_else(|| Path::new(""));
    normalize_repo_relative_path(&parent.join(target_path))
}

fn normalize_repo_relative_path(path: &Path) -> Option<String> {
    let mut parts = Vec::new();
    for component in path.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::Normal(part) => parts.push(part.to_str()?.to_string()),
            std::path::Component::ParentDir => {
                parts.pop()?;
            }
            std::path::Component::RootDir | std::path::Component::Prefix(_) => return None,
        }
    }
    if parts.is_empty() { None } else { Some(parts.join("/")) }
}

fn snapshot_dependency_origin_tree(
    spec: &DependencySpec,
    repo: &Path,
    overlay_policy: OverlayPolicy,
) -> Result<Option<String>, String> {
    let temp = tempfile::Builder::new()
        .prefix("trust-deps-materialized-snapshot-")
        .tempdir()
        .map_err(|error| format!("failed to create materialized snapshot dir: {error}"))?;
    let destination = temp.path().join("source");
    let summary =
        copy_dependency_origin_tree_with_policy(spec, repo, &destination, overlay_policy)?;
    if summary.file_count == 0 {
        return Ok(None);
    }
    snapshot_directory(&destination).map(Some)
}

fn set_executable(path: &Path) -> Result<(), String> {
    #[cfg(unix)]
    {
        let mut permissions = std::fs::metadata(path)
            .map_err(|error| format!("failed to stat {}: {error}", path.display()))?
            .permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(path, permissions)
            .map_err(|error| format!("failed to chmod {}: {error}", path.display()))?;
    }
    Ok(())
}

fn snapshot_directory(path: &Path) -> Result<String, String> {
    let mut files = Vec::new();
    let mut directories = BTreeSet::new();
    collect_directory_entries(path, Path::new(""), &mut directories, &mut files)?;
    let mut digest = Sha256::new();
    let entries =
        snapshot_entries(&directories, files.iter().map(|entry: &(String, bool, u64)| &entry.0));
    let file_map: BTreeMap<String, (bool, u64)> = files
        .iter()
        .map(|(relative, executable, len)| (relative.clone(), (*executable, *len)))
        .collect();
    for entry in entries {
        match entry {
            SnapshotEntry::Dir(relative) => {
                update_field(&mut digest, "dir");
                update_field(&mut digest, &relative);
            }
            SnapshotEntry::File(relative) => {
                let Some((executable, len)) = file_map.get(&relative) else {
                    return Err(format!("missing file metadata for {relative}"));
                };
                let content = std::fs::read(path.join(&relative))
                    .map_err(|error| format!("failed to read {relative}: {error}"))?;
                update_field(&mut digest, "file");
                update_field(&mut digest, &relative);
                update_field(&mut digest, if *executable { "755" } else { "644" });
                update_field(&mut digest, &len.to_string());
                digest.update(&content);
                digest.update(b"\0");
            }
        }
    }
    Ok(format!("sha256:{:x}", digest.finalize()))
}

fn collect_directory_entries(
    root: &Path,
    relative: &Path,
    directories: &mut BTreeSet<String>,
    files: &mut Vec<(String, bool, u64)>,
) -> Result<(), String> {
    let directory = root.join(relative);
    let mut entries = Vec::new();
    for entry in std::fs::read_dir(&directory)
        .map_err(|error| format!("failed to read {}: {error}", directory.display()))?
    {
        entries.push(entry.map_err(|error| {
            format!("failed to read entry under {}: {error}", directory.display())
        })?);
    }
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let file_type = entry.file_type().map_err(|error| {
            format!("failed to read file type for {}: {error}", entry.path().display())
        })?;
        let child_relative = relative.join(entry.file_name());
        let child_posix = child_relative.to_string_lossy().replace('\\', "/");
        if file_type.is_symlink() {
            return Err(format!("symlinks are not allowed in dependency snapshots: {child_posix}"));
        }
        if file_type.is_dir() {
            directories.insert(child_posix);
            collect_directory_entries(root, &child_relative, directories, files)?;
        } else if file_type.is_file() {
            let metadata = entry
                .metadata()
                .map_err(|error| format!("failed to stat {}: {error}", entry.path().display()))?;
            files.push((child_posix, stable_executable(&metadata), metadata.len()));
        }
    }
    Ok(())
}

fn stable_executable(metadata: &std::fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        let _ = metadata;
        false
    }
}

fn run_git_diff_no_index(cwd: &Path, left: &Path, right: &Path) -> GitOutput {
    match Command::new("git")
        .arg("-C")
        .arg(cwd)
        .args(["diff", "--no-index", "--binary", "--"])
        .arg(left)
        .arg(right)
        .output()
    {
        Ok(output) => GitOutput {
            status: output.status.code().unwrap_or(1),
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).trim().to_string(),
        },
        Err(error) => GitOutput { status: 1, stdout: String::new(), stderr: error.to_string() },
    }
}

fn parent_dir(path: &Path) -> Result<&Path, DepsError> {
    path.parent().ok_or_else(|| {
        DepsError::InvalidLock(format!("{} has no parent directory", path.display()))
    })
}

fn replace_directory_atomically(target: &Path, staged_source: &Path) -> Result<(), String> {
    let parent =
        target.parent().ok_or_else(|| format!("{} has no parent directory", target.display()))?;
    std::fs::create_dir_all(parent)
        .map_err(|error| format!("failed to create {}: {error}", parent.display()))?;
    let swap = tempfile::Builder::new()
        .prefix(".trust-deps-swap-")
        .tempdir_in(parent)
        .map_err(|error| format!("failed to create swap dir in {}: {error}", parent.display()))?;
    let replacement = swap.path().join("replacement");
    copy_filesystem_tree(staged_source, &replacement)?;
    let backup = swap.path().join("backup");
    if target.exists() {
        std::fs::rename(target, &backup).map_err(|error| {
            format!("failed to move {} to {}: {error}", target.display(), backup.display())
        })?;
    }
    if let Err(error) = std::fs::rename(&replacement, target) {
        if backup.exists() {
            let _ = std::fs::rename(&backup, target);
        }
        return Err(format!(
            "failed to move {} to {}: {error}",
            replacement.display(),
            target.display()
        ));
    }
    Ok(())
}

fn copy_filesystem_tree(source: &Path, destination: &Path) -> Result<(), String> {
    std::fs::create_dir_all(destination)
        .map_err(|error| format!("failed to create {}: {error}", destination.display()))?;
    for entry in std::fs::read_dir(source)
        .map_err(|error| format!("failed to read {}: {error}", source.display()))?
    {
        let entry = entry
            .map_err(|error| format!("failed to read entry under {}: {error}", source.display()))?;
        let target = destination.join(entry.file_name());
        let file_type = entry.file_type().map_err(|error| {
            format!("failed to read file type for {}: {error}", entry.path().display())
        })?;
        if file_type.is_symlink() {
            return Err(format!("refusing to copy symlink {}", entry.path().display()));
        }
        if file_type.is_dir() {
            copy_filesystem_tree(&entry.path(), &target)?;
        } else if file_type.is_file() {
            std::fs::copy(entry.path(), &target)
                .map_err(|error| format!("failed to copy {}: {error}", entry.path().display()))?;
            let permissions = entry
                .metadata()
                .map_err(|error| format!("failed to stat {}: {error}", entry.path().display()))?
                .permissions();
            std::fs::set_permissions(&target, permissions).map_err(|error| {
                format!("failed to set permissions on {}: {error}", target.display())
            })?;
        }
    }
    Ok(())
}

fn apply_lock_updates(lock: &mut LockFile, updates: &BTreeMap<String, (String, String)>) {
    for dependency in &mut lock.owned_dependency {
        if let Some((rev, snapshot)) = updates.get(&dependency.name) {
            dependency.rev = rev.clone();
            dependency.source_snapshot = snapshot.clone();
        }
    }
    for engine in &mut lock.engine {
        if let Some((rev, snapshot)) = updates.get(&engine.name) {
            engine.rev = rev.clone();
            engine.vendor_snapshot = snapshot.clone();
        }
    }
}

fn render_lock_file(lock: &LockFile) -> Result<String, DepsError> {
    let generated_vendor = lock.generated_vendor.as_ref().ok_or_else(|| {
        DepsError::InvalidLock("trust-engines.lock missing [generated_vendor]".to_string())
    })?;
    let mut out = String::new();
    let _ = writeln!(
        out,
        "# Generated by dpub for release candidates. Human edits are rejected by dscan."
    );
    let _ = writeln!(out, "schema = {:?}", lock.schema);
    let _ = writeln!(out);
    let _ = writeln!(out, "[generated_vendor]");
    let _ = writeln!(out, "policy = {:?}", generated_vendor.policy);
    let _ = writeln!(out, "consistency_hook = {:?}", generated_vendor.consistency_hook);
    let _ = writeln!(out);
    for engine in &lock.engine {
        let _ = writeln!(out, "[[engine]]");
        let _ = writeln!(out, "name = {:?}", engine.name);
        let _ = writeln!(out, "role = {:?}", engine.role);
        let _ = writeln!(out, "repo = {:?}", engine.repo);
        let _ = writeln!(out, "ref_kind = {:?}", engine.ref_kind);
        let _ = writeln!(out, "rev = {:?}", engine.rev);
        let _ = writeln!(out, "api = {:?}", engine.api);
        let _ = writeln!(out, "vendor_path = {:?}", engine.vendor_path);
        let _ = writeln!(out, "vendor_snapshot = {:?}", engine.vendor_snapshot);
        let _ = writeln!(out);
    }
    for dependency in &lock.owned_dependency {
        let _ = writeln!(out, "[[owned_dependency]]");
        let _ = writeln!(out, "name = {:?}", dependency.name);
        let _ = writeln!(out, "display_name = {:?}", dependency.display_name);
        let _ = writeln!(out, "role = {:?}", dependency.role);
        let _ = writeln!(out, "remote = {:?}", dependency.remote);
        let _ = writeln!(out, "ref_kind = {:?}", dependency.ref_kind);
        let _ = writeln!(out, "rev = {:?}", dependency.rev);
        let _ = writeln!(out, "path = {:?}", dependency.path);
        let _ = writeln!(out, "source_snapshot = {:?}", dependency.source_snapshot);
        let _ = writeln!(out, "status = {:?}", dependency.status);
        let _ = writeln!(out);
    }
    Ok(out)
}

fn write_file_atomically(path: &Path, content: &[u8]) -> Result<(), String> {
    let parent =
        path.parent().ok_or_else(|| format!("{} has no parent directory", path.display()))?;
    let mut temp = tempfile::Builder::new()
        .prefix(".trust-deps-lock-")
        .tempfile_in(parent)
        .map_err(|error| format!("failed to create temp file in {}: {error}", parent.display()))?;
    temp.write_all(content).map_err(|error| format!("failed to write temp lock file: {error}"))?;
    temp.flush().map_err(|error| format!("failed to flush temp lock file: {error}"))?;
    temp.persist(path)
        .map_err(|error| format!("failed to replace {}: {}", path.display(), error.error))?;
    Ok(())
}

fn load_metadata_context(root: &Path) -> MetadataContext {
    let mut context = MetadataContext::default();
    let readme_path = root.join("third_party/README.md");
    match std::fs::read_to_string(&readme_path) {
        Ok(text) => context.readme_rows = parse_readme_snapshot_rows(&text),
        Err(error) => context
            .load_errors
            .push(format!("metadata: failed to read third_party/README.md: {error}")),
    }

    let release_path = root.join("release/internal-repo-versions.toml");
    match std::fs::read_to_string(&release_path) {
        Ok(text) => match toml::from_str::<ReleaseManifest>(&text) {
            Ok(manifest) => {
                context.canonical_public_owner =
                    manifest.policy.and_then(|policy| policy.canonical_public_owner);
                context.release_repos =
                    manifest.repos.into_iter().map(|repo| (repo.id.clone(), repo)).collect();
            }
            Err(error) => context.load_errors.push(format!(
                "metadata: failed to parse release/internal-repo-versions.toml: {error}"
            )),
        },
        Err(error) => context
            .load_errors
            .push(format!("metadata: failed to read release/internal-repo-versions.toml: {error}")),
    }

    context
}

fn parse_readme_snapshot_rows(text: &str) -> BTreeMap<String, ReadmeSnapshotRow> {
    let mut rows = BTreeMap::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with('|') {
            continue;
        }
        let columns: Vec<String> = trimmed
            .trim_matches('|')
            .split('|')
            .map(|column| column.trim().trim_matches('`').to_string())
            .collect();
        if columns.len() < 3 || !columns[1].starts_with("third_party/") {
            continue;
        }
        rows.insert(
            columns[0].clone(),
            ReadmeSnapshotRow { path: columns[1].clone(), rev: columns[2].clone() },
        );
    }
    rows
}

fn inspect_dependency(
    spec: &DependencySpec,
    lock_by_name: &BTreeMap<String, OwnedDependency>,
    options: &StatusOptions,
    metadata: &MetadataContext,
) -> DependencyStatus {
    let mut errors = Vec::new();
    let mut actions = Vec::new();
    let lock_entry = lock_by_name.get(spec.name);
    let source_path =
        lock_entry.map(|entry| entry.path.clone()).unwrap_or_else(|| spec.source_path.to_string());
    let source_abs = options.root.join(&source_path);
    let clone_path = clone_path_for(spec, &options.clone_root);

    let computed_source_fingerprint =
        match snapshot_git_index_fingerprint(&options.root, &source_path) {
            Ok(Some(fingerprint)) => Some(fingerprint),
            Ok(None) => None,
            Err(error) => {
                errors.push(error);
                None
            }
        };
    let computed_source_snapshot = if options.deep_hash {
        match snapshot_git_index(&options.root, &source_path) {
            Ok(Some(snapshot)) => Some(snapshot),
            Ok(None) => {
                errors.push(format!("{} has no tracked snapshot files", source_path));
                None
            }
            Err(error) => {
                errors.push(error);
                None
            }
        }
    } else {
        None
    };

    if !source_abs.is_dir() {
        errors.push(format!("source path is not a directory: {}", source_path));
    }

    let lock_source_snapshot = lock_entry.map(|entry| entry.source_snapshot.clone());
    let source_snapshot_status = match (&lock_source_snapshot, &computed_source_snapshot) {
        (Some(lock), Some(computed))
            if normalize_snapshot(lock) == normalize_snapshot(computed) =>
        {
            SnapshotStatus::Aligned
        }
        (Some(_), Some(_)) => {
            actions.push(AlignmentAction {
                code: "refresh_lock_snapshot",
                blocking: true,
                summary: "reconcile trust-engines.lock source_snapshot with checked-in content"
                    .to_string(),
            });
            SnapshotStatus::Mismatch
        }
        (None, _) => SnapshotStatus::Missing,
        (_, None) if options.deep_hash => SnapshotStatus::Error,
        (_, None) => {
            actions.push(AlignmentAction {
                code: "deep_hash_required",
                blocking: true,
                summary: "run with --deep-hash to prove lock source_snapshot alignment".to_string(),
            });
            SnapshotStatus::Unchecked
        }
    };

    let mut clone_exists = clone_path.exists();
    let mut clone_head = None;
    let mut origin_main = None;
    let mut live_clone_status = LiveCloneStatus::Unknown;

    if !clone_exists {
        live_clone_status = LiveCloneStatus::Missing;
        actions.push(AlignmentAction {
            code: "clone_missing",
            blocking: true,
            summary: format!("create dependency clone at {}", clone_path.display()),
        });
    } else if !is_git_worktree(&clone_path) {
        live_clone_status = LiveCloneStatus::NotGitWorktree;
        actions.push(AlignmentAction {
            code: "clone_not_git_worktree",
            blocking: true,
            summary: format!("{} is not a git worktree", clone_path.display()),
        });
    } else {
        clone_exists = true;
        if options.fetch {
            let fetch = run_git(
                &clone_path,
                &["fetch", "--quiet", "origin", "+refs/heads/main:refs/remotes/origin/main"],
            );
            if fetch.status != 0 {
                errors.push(format!(
                    "failed to fetch origin/main in {}: {}",
                    clone_path.display(),
                    git_message(&fetch)
                ));
                live_clone_status = LiveCloneStatus::FetchFailed;
            }
        }

        clone_head = git_stdout(&clone_path, &["rev-parse", "HEAD"]);
        origin_main = git_stdout(
            &clone_path,
            &["rev-parse", "--verify", "refs/remotes/origin/main^{commit}"],
        );
        let dirty = git_stdout(&clone_path, &["status", "--porcelain"])
            .is_none_or(|status| !status.is_empty());
        live_clone_status = match (&clone_head, &origin_main, dirty, live_clone_status) {
            (_, _, _, LiveCloneStatus::FetchFailed) => LiveCloneStatus::FetchFailed,
            (_, _, true, _) => LiveCloneStatus::Dirty,
            (Some(head), Some(origin), false, _) if head == origin => LiveCloneStatus::Aligned,
            (Some(_), Some(_), false, _) => LiveCloneStatus::StaleCheckout,
            _ => LiveCloneStatus::Unknown,
        };

        match live_clone_status {
            LiveCloneStatus::Aligned => {}
            LiveCloneStatus::Dirty => actions.push(AlignmentAction {
                code: "clean_live_clone",
                blocking: true,
                summary: format!("clean or commit {}", clone_path.display()),
            }),
            LiveCloneStatus::StaleCheckout => actions.push(AlignmentAction {
                code: "fast_forward_live_clone",
                blocking: true,
                summary: format!("fast-forward {} to origin/main", clone_path.display()),
            }),
            LiveCloneStatus::FetchFailed => {}
            _ => actions.push(AlignmentAction {
                code: "repair_live_clone",
                blocking: true,
                summary: format!("repair live clone {}", clone_path.display()),
            }),
        }
    }

    let lock_rev = lock_entry.map(|entry| entry.rev.clone());
    let lock_current =
        matches!((&lock_rev, &origin_main), (Some(lock), Some(origin)) if lock == origin);
    if !lock_current {
        actions.push(AlignmentAction {
            code: "refresh_lock_rev",
            blocking: false,
            summary: "update trust-engines.lock rev after importing origin/main snapshot"
                .to_string(),
        });
    }

    if lock_entry.is_none() {
        errors.push(format!("missing owned_dependency entry for {}", spec.name));
    }
    if let Some(lock_entry) = lock_entry {
        validate_dependency_metadata(spec, lock_entry, metadata, &mut errors);
    }

    DependencyStatus {
        name: spec.name.to_string(),
        display_name: lock_entry
            .map(|entry| entry.display_name.clone())
            .unwrap_or_else(|| spec.display_name.to_string()),
        source_path,
        remote: lock_entry.map(|entry| entry.remote.clone()),
        lock_rev,
        lock_status: lock_entry.map(|entry| entry.status.clone()),
        lock_source_snapshot,
        computed_source_snapshot,
        computed_source_fingerprint,
        source_snapshot_status,
        clone_path: clone_path.display().to_string(),
        clone_exists,
        clone_head,
        origin_main,
        live_clone_status,
        lock_current,
        errors,
        actions,
    }
}

fn validate_dependency_metadata(
    spec: &DependencySpec,
    lock_entry: &OwnedDependency,
    metadata: &MetadataContext,
    errors: &mut Vec<String>,
) {
    errors.extend(metadata.load_errors.iter().cloned());

    let canonical_owner = metadata.canonical_public_owner.as_deref();
    if canonical_owner != Some("alabsystems") {
        errors.push(format!(
            "metadata: release/internal-repo-versions.toml policy.canonical_public_owner must be {:?}; found {:?}",
            "alabsystems", canonical_owner
        ));
    }

    let canonical_remote = canonical_remote_for(spec);
    if !same_github_identity(&lock_entry.remote, &canonical_remote) {
        errors.push(format!(
            "metadata: owned_dependency[{}].remote must identify {}; found {}",
            spec.name, canonical_remote, lock_entry.remote
        ));
    }

    let readme_project = readme_project_for(spec);
    match metadata.readme_rows.get(readme_project) {
        Some(row) => {
            if row.path != lock_entry.path {
                errors.push(format!(
                    "metadata: third_party/README.md row for {readme_project} path must match owned_dependency[{}].path: expected {}, found {}",
                    spec.name, lock_entry.path, row.path
                ));
            }
            if row.rev != lock_entry.rev {
                errors.push(format!(
                    "metadata: third_party/README.md row for {readme_project} revision must match owned_dependency[{}].rev: expected {}, found {}",
                    spec.name, lock_entry.rev, row.rev
                ));
            }
        }
        None => errors.push(format!(
            "metadata: third_party/README.md is missing a snapshot row for {readme_project}"
        )),
    }

    match metadata.release_repos.get(spec.name) {
        Some(repo) => {
            if repo.snapshot_path != lock_entry.path {
                errors.push(format!(
                    "metadata: release/internal-repo-versions.toml repos[{}].snapshot_path must match owned_dependency path: expected {}, found {}",
                    spec.name, lock_entry.path, repo.snapshot_path
                ));
            }
            if !same_github_identity(&repo.public_repo, &canonical_remote) {
                errors.push(format!(
                    "metadata: release/internal-repo-versions.toml repos[{}].public_repo must identify {}; found {}",
                    spec.name, canonical_remote, repo.public_repo
                ));
            }
            if repo.status != lock_entry.status {
                errors.push(format!(
                    "metadata: release/internal-repo-versions.toml repos[{}].status must match owned_dependency status: expected {}, found {}",
                    spec.name, lock_entry.status, repo.status
                ));
            }
            let expected_snapshot = normalize_snapshot(&lock_entry.source_snapshot);
            if repo.source_snapshot_sha256.to_ascii_lowercase() != expected_snapshot {
                errors.push(format!(
                    "metadata: release/internal-repo-versions.toml repos[{}].source_snapshot_sha256 must match owned_dependency source_snapshot: expected {}, found {}",
                    spec.name, expected_snapshot, repo.source_snapshot_sha256
                ));
            }
        }
        None => errors.push(format!(
            "metadata: release/internal-repo-versions.toml is missing [[repos]] id {:?}",
            spec.name
        )),
    }
}

fn readme_project_for(spec: &DependencySpec) -> &'static str {
    match spec.name {
        "trust_ir" | "trust-cg" => spec.display_name,
        _ => spec.name,
    }
}

fn canonical_remote_for(spec: &DependencySpec) -> String {
    // Trust: the canonical remote namespace dropped the legacy CamelCase
    // `TrustIr` path. The dependency now lives at `alabsystems/trust-ir`.
    let repo = match spec.name {
        "trust_ir" => "trust-ir",
        "trust-cg" => "trust-cg",
        other => other,
    };
    format!("https://github.com/alabsystems/{repo}")
}

fn same_github_identity(left: &str, right: &str) -> bool {
    normalize_github_identity(left) == normalize_github_identity(right)
}

fn normalize_github_identity(value: &str) -> Option<String> {
    let mut identity = value.trim();
    if let Some(stripped) = identity.strip_prefix("https://github.com/") {
        identity = stripped;
    } else if let Some(stripped) = identity.strip_prefix("git@github.com:") {
        identity = stripped;
    } else if let Some(stripped) = identity.strip_prefix("ssh://git@github.com/") {
        identity = stripped;
    } else {
        return None;
    }
    let identity = identity.split(['?', '#']).next().unwrap_or(identity).trim_end_matches(".git");
    Some(identity.to_ascii_lowercase())
}

fn clone_path_for(spec: &DependencySpec, clone_root: &Path) -> PathBuf {
    let default = clone_root.join(spec.default_clone_dir);
    if spec.name == "trust-wp" {
        let main_worktree = std::env::var_os(TRUST_WP_MAIN_WORKTREE_ENV)
            .map(PathBuf::from)
            .unwrap_or_else(|| clone_root.join("dependency-worktrees").join("trust-wp-main"));
        if main_worktree.exists() {
            return main_worktree;
        }
    }
    default
}

fn normalize_snapshot(value: &str) -> String {
    value.strip_prefix("sha256:").unwrap_or(value).to_ascii_lowercase()
}

fn is_git_worktree(path: &Path) -> bool {
    git_stdout(path, &["rev-parse", "--is-inside-work-tree"]).as_deref() == Some("true")
}

fn git_stdout(path: &Path, args: &[&str]) -> Option<String> {
    let output = run_git(path, args);
    if output.status == 0 { Some(output.stdout.trim().to_string()) } else { None }
}

fn run_git(path: &Path, args: &[&str]) -> GitOutput {
    match Command::new("git").arg("-C").arg(path).args(args).output() {
        Ok(output) => GitOutput {
            status: output.status.code().unwrap_or(1),
            stdout: String::from_utf8_lossy(&output.stdout).trim().to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).trim().to_string(),
        },
        Err(error) => GitOutput { status: 1, stdout: String::new(), stderr: error.to_string() },
    }
}

fn git_message(output: &GitOutput) -> String {
    if !output.stderr.is_empty() {
        output.stderr.clone()
    } else if !output.stdout.is_empty() {
        output.stdout.clone()
    } else {
        format!("git exited {}", output.status)
    }
}

fn snapshot_git_index(root: &Path, vendor_path: &str) -> Result<Option<String>, String> {
    let listing = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["ls-files", "--stage", "-z", "--", vendor_path])
        .output()
        .map_err(|error| format!("git ls-files failed for {vendor_path}: {error}"))?;
    if !listing.status.success() {
        return Err(format!(
            "git ls-files failed for {vendor_path}: {}",
            String::from_utf8_lossy(&listing.stderr).trim()
        ));
    }
    if listing.stdout.is_empty() {
        return Ok(None);
    }

    let mut files = Vec::new();
    let mut directories = BTreeSet::new();
    let mut symlinks = Vec::new();
    for record in listing.stdout.split(|byte| *byte == 0).filter(|record| !record.is_empty()) {
        let Some(tab) = record.iter().position(|byte| *byte == b'\t') else {
            return Err(format!("malformed git index record under {vendor_path}"));
        };
        let meta = String::from_utf8_lossy(&record[..tab]);
        let path = String::from_utf8_lossy(&record[tab + 1..]).to_string();
        let mut parts = meta.split_whitespace();
        let mode = parts.next().unwrap_or_default().to_string();
        let blob = parts.next().unwrap_or_default().to_string();
        if blob.is_empty() {
            return Err(format!("malformed git index object under {vendor_path}"));
        }
        let relative =
            path.strip_prefix(&format!("{vendor_path}/")).unwrap_or(path.as_str()).to_string();
        if mode == "120000" {
            symlinks.push(format!("{vendor_path}/{relative}"));
            continue;
        }
        if mode != "100644" && mode != "100755" {
            return Err(format!("unsupported git file mode {mode} for {vendor_path}/{relative}"));
        }
        let mut parent = Path::new(&relative).parent();
        while let Some(path) = parent {
            if path.as_os_str().is_empty() {
                break;
            }
            directories.insert(path.to_string_lossy().replace('\\', "/"));
            parent = path.parent();
        }
        files.push((relative, mode, blob));
    }

    if !symlinks.is_empty() {
        return Err(format!(
            "symlinks are not allowed in generated vendor snapshots: {}",
            symlinks.join("; ")
        ));
    }
    if files.is_empty() {
        return Ok(None);
    }

    files.sort_by(|left, right| left.0.cmp(&right.0));
    let blobs: BTreeMap<String, (String, String)> = files
        .iter()
        .map(|(path, mode, blob)| (path.clone(), (mode.clone(), blob.clone())))
        .collect();
    let entries = snapshot_entries(&directories, blobs.keys());

    let mut digest = Sha256::new();
    let mut blob_reader = GitBlobReader::new(root)?;
    for entry in entries {
        match entry {
            SnapshotEntry::Dir(path) => {
                update_field(&mut digest, "dir");
                update_field(&mut digest, &path);
            }
            SnapshotEntry::File(path) => {
                let Some((mode, blob)) = blobs.get(&path) else {
                    return Err(format!("missing blob for {vendor_path}/{path}"));
                };
                let content = blob_reader.read_blob(blob)?;
                update_field(&mut digest, "file");
                update_field(&mut digest, &path);
                update_field(&mut digest, if mode == "100755" { "755" } else { "644" });
                update_field(&mut digest, &content.len().to_string());
                digest.update(&content);
                digest.update(b"\0");
            }
        }
    }

    Ok(Some(format!("sha256:{:x}", digest.finalize())))
}

fn snapshot_git_index_fingerprint(
    root: &Path,
    vendor_path: &str,
) -> Result<Option<String>, String> {
    let listing = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["ls-files", "--stage", "-z", "--", vendor_path])
        .output()
        .map_err(|error| format!("git ls-files failed for {vendor_path}: {error}"))?;
    if !listing.status.success() {
        return Err(format!(
            "git ls-files failed for {vendor_path}: {}",
            String::from_utf8_lossy(&listing.stderr).trim()
        ));
    }
    if listing.stdout.is_empty() {
        return Ok(None);
    }

    let mut digest = Sha256::new();
    let mut included = false;
    for record in listing.stdout.split(|byte| *byte == 0).filter(|record| !record.is_empty()) {
        let Some(_tab) = record.iter().position(|byte| *byte == b'\t') else {
            return Err(format!("malformed git index record under {vendor_path}"));
        };
        included = true;
        digest.update(record);
        digest.update(b"\0");
    }
    if !included {
        return Ok(None);
    }
    Ok(Some(format!("git-index-sha256:{:x}", digest.finalize())))
}

#[derive(Debug)]
enum SnapshotEntry {
    Dir(String),
    File(String),
}

#[derive(Debug, Default)]
struct SnapshotNode {
    children: BTreeMap<String, SnapshotTreeEntry>,
}

#[derive(Debug)]
enum SnapshotTreeEntry {
    Dir(SnapshotNode),
    File(String),
}

fn snapshot_entries<'a>(
    directories: &BTreeSet<String>,
    files: impl Iterator<Item = &'a String>,
) -> Vec<SnapshotEntry> {
    let mut root = SnapshotNode::default();
    for directory in directories {
        insert_dir(&mut root, directory);
    }
    for file in files {
        insert_file(&mut root, file);
    }

    let mut entries = Vec::new();
    emit_entries("", &root, &mut entries);
    entries
}

fn insert_dir(root: &mut SnapshotNode, path: &str) {
    let mut node = root;
    for component in path.split('/') {
        node = match node
            .children
            .entry(component.to_string())
            .or_insert_with(|| SnapshotTreeEntry::Dir(SnapshotNode::default()))
        {
            SnapshotTreeEntry::Dir(child) => child,
            SnapshotTreeEntry::File(_) => return,
        };
    }
}

fn insert_file(root: &mut SnapshotNode, path: &str) {
    let mut node = root;
    let mut components = path.split('/').peekable();
    while let Some(component) = components.next() {
        if components.peek().is_none() {
            node.children.insert(component.to_string(), SnapshotTreeEntry::File(path.to_string()));
            return;
        }
        node = match node
            .children
            .entry(component.to_string())
            .or_insert_with(|| SnapshotTreeEntry::Dir(SnapshotNode::default()))
        {
            SnapshotTreeEntry::Dir(child) => child,
            SnapshotTreeEntry::File(_) => return,
        };
    }
}

fn emit_entries(prefix: &str, node: &SnapshotNode, entries: &mut Vec<SnapshotEntry>) {
    for (name, entry) in &node.children {
        let path = if prefix.is_empty() { name.clone() } else { format!("{prefix}/{name}") };
        match entry {
            SnapshotTreeEntry::Dir(child) => {
                entries.push(SnapshotEntry::Dir(path.clone()));
                emit_entries(&path, child, entries);
            }
            SnapshotTreeEntry::File(file) => entries.push(SnapshotEntry::File(file.clone())),
        }
    }
}

fn update_field(digest: &mut Sha256, value: &str) {
    digest.update(value.as_bytes());
    digest.update(b"\0");
}

struct GitBlobReader {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl GitBlobReader {
    fn new(root: &Path) -> Result<Self, String> {
        let mut child = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(["cat-file", "--batch"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|error| format!("git cat-file --batch failed: {error}"))?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| "git cat-file --batch stdin unavailable".to_string())?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| "git cat-file --batch stdout unavailable".to_string())?;
        Ok(Self { child, stdin, stdout: BufReader::new(stdout) })
    }

    fn read_blob(&mut self, blob: &str) -> Result<Vec<u8>, String> {
        writeln!(self.stdin, "{blob}")
            .map_err(|error| format!("git cat-file --batch write failed for {blob}: {error}"))?;
        self.stdin
            .flush()
            .map_err(|error| format!("git cat-file --batch flush failed for {blob}: {error}"))?;

        let mut header = String::new();
        self.stdout
            .read_line(&mut header)
            .map_err(|error| format!("git cat-file --batch read failed for {blob}: {error}"))?;
        let fields: Vec<&str> = header.split_whitespace().collect();
        if fields.len() != 3 || fields[1] != "blob" {
            return Err(format!("git cat-file returned non-blob object for {blob}: {header:?}"));
        }
        let size: usize = fields[2]
            .parse()
            .map_err(|error| format!("git cat-file returned invalid size for {blob}: {error}"))?;
        let mut content = vec![0; size];
        self.stdout
            .read_exact(&mut content)
            .map_err(|error| format!("git cat-file returned truncated blob {blob}: {error}"))?;
        let mut trailing = [0; 1];
        self.stdout.read_exact(&mut trailing).map_err(|error| {
            format!("git cat-file missing trailing newline for {blob}: {error}")
        })?;
        if trailing != [b'\n'] {
            return Err(format!("git cat-file malformed trailing byte for {blob}"));
        }
        Ok(content)
    }
}

impl Drop for GitBlobReader {
    fn drop(&mut self) {
        let _ = self.stdin.flush();
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalize_snapshot_accepts_prefix() {
        assert_eq!(normalize_snapshot("sha256:ABCDEF"), "abcdef",);
    }

    #[test]
    fn unchecked_snapshot_blocks_status_success() {
        assert!(SnapshotStatus::Unchecked.is_blocking());
        assert!(SnapshotStatus::Mismatch.is_blocking());
        let dependency = DependencyStatus {
            name: "ty".to_string(),
            display_name: "TY".to_string(),
            source_path: "first-party/ty".to_string(),
            remote: Some("git@example/ty".to_string()),
            lock_rev: Some("head".to_string()),
            lock_status: Some("planned".to_string()),
            lock_source_snapshot: Some("sha256:old".to_string()),
            computed_source_snapshot: None,
            computed_source_fingerprint: Some("git-index-sha256:fast".to_string()),
            source_snapshot_status: SnapshotStatus::Unchecked,
            clone_path: "/tmp/ty".to_string(),
            clone_exists: true,
            clone_head: Some("head".to_string()),
            origin_main: Some("head".to_string()),
            live_clone_status: LiveCloneStatus::Aligned,
            lock_current: true,
            errors: Vec::new(),
            actions: vec![AlignmentAction {
                code: "deep_hash_required",
                blocking: true,
                summary: "run with --deep-hash".to_string(),
            }],
        };

        assert!(!dependency.ok());
    }

    #[test]
    fn text_report_includes_dependency_names() {
        let report = AlignmentReport {
            schema: "trust.deps.alignment.v1",
            root: ".".to_string(),
            lock_file: "trust-engines.lock".to_string(),
            fetch: false,
            summary: AlignmentSummary {
                total: 1,
                ok: 0,
                failed: 1,
                stale_lock: 1,
                snapshot_mismatch: 1,
                live_clone_misaligned: 0,
                dirty_live_clone: 0,
                metadata_mismatch: 0,
            },
            dependencies: vec![DependencyStatus {
                name: "trust-mc".to_string(),
                display_name: "trust-mc".to_string(),
                source_path: "../trust-mc".to_string(),
                remote: Some("git@example/trust-mc".to_string()),
                lock_rev: Some("old".to_string()),
                lock_status: Some("planned".to_string()),
                lock_source_snapshot: Some("sha256:old".to_string()),
                computed_source_snapshot: Some("sha256:new".to_string()),
                computed_source_fingerprint: Some("git-index-sha256:fast".to_string()),
                source_snapshot_status: SnapshotStatus::Mismatch,
                clone_path: "/tmp/trust-mc".to_string(),
                clone_exists: true,
                clone_head: Some("new".to_string()),
                origin_main: Some("new".to_string()),
                live_clone_status: LiveCloneStatus::Aligned,
                lock_current: false,
                errors: vec!["snapshot mismatch".to_string()],
                actions: vec![AlignmentAction {
                    code: "refresh_lock_snapshot",
                    blocking: true,
                    summary: "refresh".to_string(),
                }],
            }],
        };
        let rendered = render_text(&report);
        assert!(rendered.contains("trust-mc"));
        assert!(rendered.contains("lock_status: planned"));
        assert!(rendered.contains("snapshot mismatch"));
    }

    #[test]
    fn metadata_validation_rejects_legacy_remote_namespace() {
        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "trust_ir").expect("trust_ir spec");
        let lock_entry = OwnedDependency {
            name: "trust_ir".to_string(),
            display_name: "TrustIr".to_string(),
            role: "verification-ir".to_string(),
            remote: "https://github.com/alabsystems/TrustIr".to_string(),
            ref_kind: "commit".to_string(),
            rev: "1111111111111111111111111111111111111111".to_string(),
            path: "third_party/trust_ir".to_string(),
            source_snapshot: format!("sha256:{}", "2".repeat(64)),
            status: "planned".to_string(),
        };
        let mut metadata = MetadataContext {
            canonical_public_owner: Some("alabsystems".to_string()),
            ..MetadataContext::default()
        };
        metadata.readme_rows.insert(
            "TrustIr".to_string(),
            ReadmeSnapshotRow {
                path: "third_party/trust_ir".to_string(),
                rev: lock_entry.rev.clone(),
            },
        );
        metadata.release_repos.insert(
            "trust_ir".to_string(),
            ReleaseRepo {
                id: "trust_ir".to_string(),
                snapshot_path: "third_party/trust_ir".to_string(),
                source_snapshot_sha256: "2".repeat(64),
                public_repo: "https://github.com/alabsystems/TrustIr".to_string(),
                status: "planned".to_string(),
            },
        );

        let mut errors = Vec::new();
        validate_dependency_metadata(spec, &lock_entry, &metadata, &mut errors);

        assert!(
            errors.iter().any(|error| error.contains("owned_dependency[trust_ir].remote")),
            "{errors:?}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn export_reports_symlink_policy_violation_per_dependency() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().expect("tempdir");
        let root = temp.path().join("root");
        let vendor = root.join("third_party/trust_ir");
        std::fs::create_dir_all(&vendor).expect("vendor dir");
        std::fs::write(vendor.join("README.md"), "vendored\n").expect("vendor file");
        init_git_repo(&root);
        git(&root, &["add", "."]);
        git(&root, &["commit", "-q", "-m", "vendor"]);

        std::fs::write(
            root.join("trust-engines.lock"),
            r#"
schema = "trust.engines.lock.v2"

[generated_vendor]
policy = "committed-generated-snapshot-v1"
consistency_hook = "test-hook"

[[owned_dependency]]
name = "trust_ir"
display_name = "TrustIr"
role = "verification-ir"
remote = "file:///tmp/TrustIr"
ref_kind = "commit"
rev = "old"
path = "third_party/trust_ir"
source_snapshot = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
status = "planned"
"#,
        )
        .expect("lock file");

        let clone_root = temp.path().join("clones");
        let origin = clone_root.join("TrustIr");
        std::fs::create_dir_all(&origin).expect("origin dir");
        init_git_repo(&origin);
        std::fs::write(origin.join("README.md"), "origin\n").expect("origin file");
        symlink("flags-target", origin.join(".flags")).expect("origin symlink");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);
        let head = git_stdout_required(&origin, &["rev-parse", "HEAD"]);
        git(&origin, &["update-ref", "refs/remotes/origin/main", &head]);

        let mut options = MutationOptions::for_root(&root);
        options.clone_root = clone_root;
        options.dependencies.push("trust_ir".to_string());

        let report = run_export_transaction(&options).expect("transaction report");
        assert_eq!(report.summary.total, 1);
        assert_eq!(report.summary.failed, 1);
        let dependency = &report.dependencies[0];
        assert_eq!(dependency.name, "trust_ir");
        assert_eq!(dependency.status, "blocked");
        assert!(
            dependency.errors.iter().any(|error| error.contains("symlink target is not tracked")),
            "{:?}",
            dependency.errors
        );
    }

    #[cfg(unix)]
    #[test]
    fn trust_vc_origin_import_applies_no_overlay() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::write(
            origin.join("Cargo.toml"),
            r#"
[workspace.dependencies]
solver-core = { git = "https://github.com/example/solver-core", rev = "abc" }
proof-core = { git = "https://github.com/example/proof-core", rev = "def" }
"#,
        )
        .expect("workspace manifest");
        std::fs::write(
            origin.join("Cargo.lock"),
            r#"
[[package]]
name = "proof-core"
version = "0.9.0"
source = "git+https://github.com/example/proof-core?rev=def#def"
dependencies = [
 "num-bigint 0.4.6 (git+https://github.com/example/proof-core?rev=def)",
 "solver-core",
]

[[package]]
name = "external"
version = "1.0.0"
source = "git+https://example.invalid/external?rev=keep#keep"
dependencies = [
 "other 1.0.0 (git+https://example.invalid/external?rev=keep)",
]
"#,
        )
        .expect("lock file");
        std::fs::create_dir_all(origin.join("evals/verus/ported/cargo_fixture"))
            .expect("fixture dir");
        std::fs::write(
            origin.join("evals/verus/ported/cargo_fixture/Cargo.lock"),
            r#"
[[package]]
name = "solver-core"
version = "0.10.0"
source = "git+https://github.com/example/solver-core?rev=abc#abc"
dependencies = [
 "num-traits 0.2.19 (git+https://github.com/example/solver-core?rev=abc)",
]
"#,
        )
        .expect("fixture lock");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "trust-vc").expect("trust-vc spec");
        let destination = temp.path().join("snapshot");
        let summary =
            copy_dependency_origin_tree(spec, &origin, &destination).expect("trust-vc overlay");

        assert_eq!(summary.file_count, 3);
        let manifest =
            std::fs::read_to_string(destination.join("Cargo.toml")).expect("workspace manifest");
        assert!(manifest.contains(
            r#"solver-core = { git = "https://github.com/example/solver-core", rev = "abc" }"#
        ));
        assert!(manifest.contains(
            r#"proof-core = { git = "https://github.com/example/proof-core", rev = "def" }"#
        ));
        let lock = std::fs::read_to_string(destination.join("Cargo.lock")).expect("lock file");
        assert!(lock.contains("github.com/example/proof-core"));
        assert!(lock.contains(
            r#""num-bigint 0.4.6 (git+https://github.com/example/proof-core?rev=def)","#
        ));
        assert!(lock.contains("https://example.invalid/external"));
        assert!(lock.contains(r#""other 1.0.0 (git+https://example.invalid/external?rev=keep)","#));
        let fixture_lock = std::fs::read_to_string(
            destination.join("evals/verus/ported/cargo_fixture/Cargo.lock"),
        )
        .expect("fixture lock file");
        assert!(fixture_lock.contains("github.com/example/solver-core"));
        assert!(fixture_lock.contains(
            r#""num-traits 0.2.19 (git+https://github.com/example/solver-core?rev=abc)","#
        ));
    }

    #[cfg(unix)]
    #[test]
    fn origin_import_rejects_owned_cargo_manifest_git_sources_after_overlay() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::write(
            origin.join("Cargo.toml"),
            r#"
[workspace.dependencies]
trust-ir = { git = "ssh://git@github.com:22/alabsystems/trust_ir.git", rev = "def" }
"#,
        )
        .expect("workspace manifest");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "trust-vc").expect("trust-vc spec");
        let destination = temp.path().join("snapshot");
        let error = copy_dependency_origin_tree(spec, &origin, &destination)
            .expect_err("owned manifest git sources must be rejected");

        assert!(error.contains("Cargo.toml:3"), "{error}");
        assert!(
            error.contains("owned snapshot Cargo manifest must not contain owned git dependency"),
            "{error}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn origin_import_rejects_owned_cargo_lock_git_sources_after_overlay() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::write(origin.join("Cargo.toml"), "[package]\nname = \"trust-vc-fixture\"\n")
            .expect("manifest");
        std::fs::write(
            origin.join("Cargo.lock"),
            r#"
[[package]]
name = "ay"
version = "0.10.0"
source = "git+ssh://git@github.com:22/alabsystems/ay.git?rev=abc#abc"
"#,
        )
        .expect("lock file");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "trust-vc").expect("trust-vc spec");
        let destination = temp.path().join("snapshot");
        let error = copy_dependency_origin_tree(spec, &origin, &destination)
            .expect_err("owned lock git sources must be rejected");

        assert!(error.contains("Cargo.lock:5"), "{error}");
        assert!(
            error.contains("owned snapshot Cargo.lock must not contain owned git source identity"),
            "{error}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn trust_wp_origin_overlay_copies_trust_manifest_and_lock_only() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::create_dir_all(origin.join("dependency-modes/trust")).expect("mode dir");
        std::fs::write(origin.join("Cargo.toml"), "[package]\nname = \"upstream-trust-wp\"\n")
            .expect("root manifest");
        std::fs::write(origin.join("Cargo.lock"), "# upstream lock\n").expect("root lock");
        std::fs::write(
            origin.join("dependency-modes/trust/Cargo.toml"),
            "[package]\nname = \"trust-wp\"\n",
        )
        .expect("trust manifest");
        std::fs::write(origin.join("dependency-modes/trust/Cargo.lock"), "# trust lock\n")
            .expect("trust lock");
        std::fs::write(origin.join("dependency-modes/trust/extra.txt"), "mode-only\n")
            .expect("mode extra");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "trust-wp").expect("trust-wp spec");
        let destination = temp.path().join("snapshot");
        let summary = copy_dependency_origin_tree_with_policy(
            spec,
            &origin,
            &destination,
            OverlayPolicy::Bootstrap,
        )
        .expect("trust-wp overlay");

        assert_eq!(summary.file_count, 5);
        let manifest = std::fs::read_to_string(destination.join("Cargo.toml")).expect("manifest");
        let lock = std::fs::read_to_string(destination.join("Cargo.lock")).expect("lock");
        assert!(manifest.contains("trust-wp"), "{manifest}");
        assert_eq!(lock, "# trust lock\n");
        assert!(!destination.join("extra.txt").exists());
        assert_eq!(
            std::fs::read_to_string(destination.join("dependency-modes/trust/extra.txt"))
                .expect("mode extra"),
            "mode-only\n"
        );
    }

    #[cfg(unix)]
    #[test]
    fn trust_mc_origin_overlay_copies_trust_mode_contents() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::create_dir_all(origin.join("dependency-modes/trust/config"))
            .expect("mode config dir");
        std::fs::write(origin.join("Cargo.toml"), "[package]\nname = \"upstream-trust-mc\"\n")
            .expect("root manifest");
        std::fs::write(
            origin.join("dependency-modes/trust/Cargo.toml"),
            "[package]\nname = \"trust-mc\"\n",
        )
        .expect("trust manifest");
        std::fs::write(origin.join("dependency-modes/trust/config/trust_mc.toml"), "mode = true\n")
            .expect("mode config");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "trust-mc").expect("trust-mc spec");
        let destination = temp.path().join("snapshot");
        let summary = copy_dependency_origin_tree_with_policy(
            spec,
            &origin,
            &destination,
            OverlayPolicy::Bootstrap,
        )
        .expect("trust-mc overlay");

        assert_eq!(summary.file_count, 4);
        let manifest = std::fs::read_to_string(destination.join("Cargo.toml")).expect("manifest");
        assert!(manifest.contains("trust-mc"), "{manifest}");
        assert_eq!(
            std::fs::read_to_string(destination.join("config/trust_mc.toml")).expect("mode config"),
            "mode = true\n"
        );
        assert_eq!(
            std::fs::read_to_string(destination.join("dependency-modes/trust/Cargo.toml"))
                .expect("preserved mode manifest"),
            "[package]\nname = \"trust-mc\"\n"
        );
    }

    #[cfg(unix)]
    #[test]
    fn trust_cg_origin_overlay_copies_trust_mode_contents_and_preserves_source() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::create_dir_all(
            origin.join("dependency-modes/trust/crates/rustc_codegen_trust_cg"),
        )
        .expect("mode codegen dir");
        std::fs::write(origin.join("Cargo.toml"), "[package]\nname = \"upstream-trust_cg\"\n")
            .expect("root manifest");
        std::fs::write(
            origin.join("dependency-modes/trust/Cargo.toml"),
            "[package]\nname = \"trust-cg\"\n",
        )
        .expect("trust manifest");
        std::fs::write(
            origin.join("dependency-modes/trust/crates/rustc_codegen_trust_cg/Cargo.toml"),
            "[package]\nname = \"trust-codegen\"\n",
        )
        .expect("trust codegen manifest");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "trust-cg").expect("trust_cg spec");
        let destination = temp.path().join("snapshot");
        let summary = copy_dependency_origin_tree_with_policy(
            spec,
            &origin,
            &destination,
            OverlayPolicy::Bootstrap,
        )
        .expect("trust_cg overlay");

        assert_eq!(summary.file_count, 4);
        let manifest = std::fs::read_to_string(destination.join("Cargo.toml")).expect("manifest");
        assert!(manifest.contains("trust-cg"), "{manifest}");
        let codegen_manifest =
            std::fs::read_to_string(destination.join("crates/rustc_codegen_trust_cg/Cargo.toml"))
                .expect("codegen manifest");
        assert!(codegen_manifest.contains("trust-codegen"), "{codegen_manifest}");
        assert!(destination.join("dependency-modes/trust/Cargo.toml").exists());
        assert!(
            destination
                .join("dependency-modes/trust/crates/rustc_codegen_trust_cg/Cargo.toml")
                .exists()
        );
    }

    #[cfg(unix)]
    #[test]
    fn ty_origin_overlay_consumes_trust_toml_contract() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::create_dir_all(origin.join("dependency-modes")).expect("mode dir");
        std::fs::write(
            origin.join("Cargo.toml"),
            r#"
[workspace.dependencies]
ay = { git = "https://github.com/alabsystems/ay", rev = "abc", default-features = false }
trust-ir = { git = "ssh://git@github.com/alabsystems/trust_ir.git", rev = "def" }
trust-ir-build = { git = "ssh://git@github.com/alabsystems/trust_ir.git", rev = "def" }

[patch."ssh://git@github.com/alabsystems/trust_ir.git"]
trust-ir = { git = "ssh://git@github.com:22/alabsystems/trust_ir.git", rev = "def" }
trust-ir-build = { git = "ssh://git@github.com:22/alabsystems/trust_ir.git", rev = "def" }
"#,
        )
        .expect("root manifest");
        std::fs::write(
            origin.join("Cargo.lock"),
            r#"
[[package]]
name = "trust_ir"
version = "0.1.0"
source = "git+ssh://git@github.com:22/alabsystems/trust_ir.git?rev=def#def"

[[package]]
name = "ay"
version = "0.10.0"
source = "git+https://github.com/alabsystems/ay?rev=abc#abc"
dependencies = [
 "trust_ir 0.1.0 (git+ssh://git@github.com:22/alabsystems/trust_ir.git?rev=def)",
]
"#,
        )
        .expect("lock");
        std::fs::write(
            origin.join("dependency-modes/trust.toml"),
            r#"
schema = "ty.dependency-mode.trust.v1"

[trust]
lockfile_policy = "regenerate-after-rewrite"

[[trust.replacements]]
source = "https://github.com/alabsystems/ay"
default_relative_path = "../ay"
packages = ["ay"]

[[trust.replacements]]
source = "ssh://git@github.com/alabsystems/trust_ir.git"
patched_source = "ssh://git@github.com:22/alabsystems/trust_ir.git"
default_relative_path = "../trust-ir"
packages = ["trust-ir", "trust-ir-build"]
"#,
        )
        .expect("trust contract");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "ty").expect("ty spec");
        let destination = temp.path().join("snapshot");
        let summary = copy_dependency_origin_tree_with_policy(
            spec,
            &origin,
            &destination,
            OverlayPolicy::Bootstrap,
        )
        .expect("ty mode");

        assert_eq!(summary.file_count, 3);
        let manifest = std::fs::read_to_string(destination.join("Cargo.toml")).expect("manifest");
        let lock = std::fs::read_to_string(destination.join("Cargo.lock")).expect("lock");
        assert!(
            manifest.contains(r#"ay = { path = "../ay/crates/ay", default-features = false }"#),
            "{manifest}"
        );
        assert!(
            manifest.contains(r#"trust-ir = { path = "../trust-ir/crates/trust-ir" }"#),
            "{manifest}"
        );
        assert!(
            manifest.contains(r#"trust-ir-build = { path = "../trust-ir/crates/trust-ir-build" }"#),
            "{manifest}"
        );
        assert!(!manifest.contains("git ="), "{manifest}");
        assert!(!lock.contains("git+"), "{lock}");
    }

    #[cfg(unix)]
    #[test]
    fn ty_origin_overlay_prefers_checked_in_trust_directory() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::create_dir_all(origin.join("dependency-modes/trust")).expect("mode dir");
        std::fs::write(origin.join("Cargo.toml"), "[package]\nname = \"upstream-ty\"\n")
            .expect("root manifest");
        std::fs::write(
            origin.join("dependency-modes/trust.toml"),
            "[package]\nname = \"trust-ty-file\"\n",
        )
        .expect("trust manifest file");
        std::fs::write(
            origin.join("dependency-modes/trust/Cargo.toml"),
            "[package]\nname = \"trust-ty-directory\"\n",
        )
        .expect("trust manifest directory");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "ty").expect("ty spec");
        let destination = temp.path().join("snapshot");
        let summary = copy_dependency_origin_tree_with_policy(
            spec,
            &origin,
            &destination,
            OverlayPolicy::Bootstrap,
        )
        .expect("ty mode");

        assert_eq!(summary.file_count, 3);
        let manifest = std::fs::read_to_string(destination.join("Cargo.toml")).expect("manifest");
        assert!(manifest.contains("trust-ty-directory"), "{manifest}");
    }

    #[cfg(unix)]
    #[test]
    fn ay_origin_overlay_uses_trust_mode_assets_when_present() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::create_dir_all(origin.join("dependency-modes/trust/crates/ay-jit"))
            .expect("mode dir");
        std::fs::write(
            origin.join("Cargo.toml"),
            "[workspace.dependencies]\ntrust_ir = { git = \"ssh://git@github.com/alabsystems/trust_ir.git\", rev = \"def\" }\n",
        )
        .expect("root manifest");
        std::fs::write(
            origin.join("dependency-modes/trust/Cargo.toml"),
            "[package]\nname = \"trust-ay\"\n",
        )
        .expect("trust manifest");
        std::fs::write(origin.join("dependency-modes/trust/Cargo.lock"), "# trust lock\n")
            .expect("trust lock");
        std::fs::write(
            origin.join("dependency-modes/trust/crates/ay-jit/Cargo.toml"),
            "[package]\nname = \"trust-ay-jit\"\n",
        )
        .expect("trust jit manifest");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "ay").expect("ay spec");
        let destination = temp.path().join("snapshot");
        let summary = copy_dependency_origin_tree_with_policy(
            spec,
            &origin,
            &destination,
            OverlayPolicy::Bootstrap,
        )
        .expect("ay mode");

        assert_eq!(summary.file_count, 6);
        let manifest = std::fs::read_to_string(destination.join("Cargo.toml")).expect("manifest");
        assert!(manifest.contains("trust-ay"), "{manifest}");
        assert!(!manifest.contains("alabsystems/TrustIr"));
        let jit_manifest = std::fs::read_to_string(destination.join("crates/ay-jit/Cargo.toml"))
            .expect("trust jit manifest");
        assert!(jit_manifest.contains("trust-ay-jit"), "{jit_manifest}");
    }

    #[cfg(unix)]
    #[test]
    fn ay_origin_overlay_rewrites_monorepo_dependency_envelope_without_mode_assets() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::create_dir_all(origin.join("crates/ay-jit")).expect("ay-jit dir");
        std::fs::write(
            origin.join("Cargo.toml"),
            r#"
[workspace.dependencies]
trust-ir = { version = "0.1.0", git = "ssh://git@github.com/alabsystems/trust_ir.git", rev = "def", features = ["serde", "parser"] }

[patch."ssh://git@github.com/alabsystems/trust_ir.git"]
trust-ir-build = { git = "ssh://git@github.com:22/alabsystems/trust_ir.git", rev = "def" }
"#,
        )
        .expect("workspace manifest");
        std::fs::write(
            origin.join("crates/ay-jit/Cargo.toml"),
            r#"
[dependencies]
trust-cg-codegen = { version = "0.1.0", git = "ssh://git@github.com/alabsystems/trust_cg.git", rev = "abc", default-features = false, optional = true }
"#,
        )
        .expect("jit manifest");
        std::fs::write(
            origin.join("Cargo.lock"),
            r#"
[[package]]
name = "trust-cg-codegen"
version = "0.1.0"
source = "git+ssh://git@github.com/alabsystems/trust_cg.git?rev=abc#abc"

[[package]]
name = "trust_ir"
version = "0.1.0"
source = "git+ssh://git@github.com/alabsystems/trust_ir.git?rev=def#def"

[[package]]
name = "trust_ir-build"
version = "0.1.0"
source = "git+ssh://git@github.com:22/alabsystems/trust_ir.git?rev=def#def"
"#,
        )
        .expect("lock file");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let spec = DEPENDENCIES.iter().find(|spec| spec.name == "ay").expect("ay spec");
        let destination = temp.path().join("snapshot");
        let summary = copy_dependency_origin_tree_with_policy(
            spec,
            &origin,
            &destination,
            OverlayPolicy::Bootstrap,
        )
        .expect("ay overlay");

        assert_eq!(summary.file_count, 3);
        let manifest =
            std::fs::read_to_string(destination.join("Cargo.toml")).expect("workspace manifest");
        assert!(
            manifest.contains(
                r#"trust-ir = { version = "0.1.0", path = "../trust-ir/crates/trust-ir", features = ["serde", "parser"] }"#
            ),
            "{manifest}"
        );
        assert!(
            manifest.contains(r#"trust-ir-build = { path = "../trust-ir/crates/trust-ir-build" }"#),
            "{manifest}"
        );
        let jit_manifest = std::fs::read_to_string(destination.join("crates/ay-jit/Cargo.toml"))
            .expect("jit manifest");
        assert!(
            jit_manifest.contains(
                r#"trust-cg-codegen = { version = "0.1.0", path = "../../../trust-codegen/crates/trust-cg-codegen", default-features = false, optional = true }"#
            ),
            "{jit_manifest}"
        );
        let lock = std::fs::read_to_string(destination.join("Cargo.lock")).expect("lock file");
        assert!(!lock.contains("github.com/alabsystems/trust-cg"));
        assert!(!lock.contains("github.com/alabsystems/TrustIr"));
        assert!(!lock.contains("github.com:22/alabsystems/TrustIr"));
    }

    #[cfg(unix)]
    #[test]
    fn copy_git_tracked_tree_excludes_repo_management_scaffolding() {
        let temp = tempfile::tempdir().expect("tempdir");
        let origin = temp.path().join("origin");
        init_git_repo(&origin);
        std::fs::create_dir_all(origin.join("crates/core/src")).expect("source dir");
        std::fs::write(origin.join("crates/core/src/lib.rs"), "pub fn ok() {}\n")
            .expect("source file");
        std::fs::create_dir_all(origin.join(".claude")).expect("claude dir");
        std::fs::write(origin.join(".claude/settings.json"), "{}\n").expect("claude file");
        std::fs::create_dir_all(origin.join("crates/core/.claude")).expect("nested claude dir");
        std::fs::write(origin.join("crates/core/.claude/state.json"), "{}\n")
            .expect("nested claude file");
        std::fs::create_dir_all(origin.join(".github/workflows")).expect("github dir");
        std::fs::write(origin.join(".github/workflows/ci.yml"), "name: ci\n").expect("github file");
        std::fs::create_dir_all(origin.join(".issues")).expect("issues dir");
        std::fs::write(origin.join(".issues/1.md"), "issue\n").expect("issue file");
        std::fs::create_dir_all(origin.join(".pre-commit-local.d")).expect("precommit dir");
        std::fs::write(origin.join(".pre-commit-local.d/check.sh"), "#!/bin/sh\n")
            .expect("precommit file");
        std::fs::create_dir_all(origin.join("reports")).expect("reports dir");
        std::fs::write(origin.join("reports/run.md"), "generated\n").expect("report file");
        std::fs::create_dir_all(origin.join("benchmarks/templates")).expect("bench template dir");
        std::fs::write(origin.join("benchmarks/templates/case.rs"), "fn main() {}\n")
            .expect("bench template file");
        std::fs::write(origin.join(".gitattributes"), "* text=auto\n").expect("gitattributes");
        std::fs::write(origin.join(".gitignore"), "target\n").expect("gitignore");
        std::fs::write(origin.join(".manager_1_files.json"), "{}\n").expect("manager state");
        std::fs::write(origin.join(".worker_prover_1_files.json.stale"), "{}\n")
            .expect("worker state");
        std::fs::write(origin.join("rust_out"), "generated\n").expect("rust_out");
        std::fs::write(origin.join("AGENTS.md"), "agent instructions\n").expect("agents");
        std::fs::write(origin.join("crates/core/AGENTS.md"), "nested instructions\n")
            .expect("nested agents");
        git(&origin, &["add", "."]);
        git(&origin, &["commit", "-q", "-m", "origin"]);

        let destination = temp.path().join("snapshot");
        let summary =
            copy_git_tracked_tree(&origin, None, &destination).expect("filtered snapshot copy");

        assert_eq!(summary.file_count, 1);
        assert!(destination.join("crates/core/src/lib.rs").exists());
        assert!(!destination.join(".claude/settings.json").exists());
        assert!(!destination.join("crates/core/.claude/state.json").exists());
        assert!(!destination.join(".github/workflows/ci.yml").exists());
        assert!(!destination.join(".issues/1.md").exists());
        assert!(!destination.join(".pre-commit-local.d/check.sh").exists());
        assert!(!destination.join("reports/run.md").exists());
        assert!(!destination.join("benchmarks/templates/case.rs").exists());
        assert!(!destination.join(".gitattributes").exists());
        assert!(!destination.join(".gitignore").exists());
        assert!(!destination.join(".manager_1_files.json").exists());
        assert!(!destination.join(".worker_prover_1_files.json.stale").exists());
        assert!(!destination.join("rust_out").exists());
        assert!(!destination.join("AGENTS.md").exists());
        assert!(!destination.join("crates/core/AGENTS.md").exists());
    }

    #[cfg(unix)]
    fn init_git_repo(path: &Path) {
        std::fs::create_dir_all(path).expect("repo dir");
        git(path, &["init", "-q", "--initial-branch=main"]);
        git(path, &["config", "user.email", "trust-deps-test@example.invalid"]);
        git(path, &["config", "user.name", "trust-deps test"]);
    }

    #[cfg(unix)]
    fn git(path: &Path, args: &[&str]) {
        let output =
            Command::new("git").arg("-C").arg(path).args(args).output().expect("git command");
        assert!(
            output.status.success(),
            "git -C {} {:?}\nstdout:\n{}\nstderr:\n{}",
            path.display(),
            args,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[cfg(unix)]
    fn git_stdout_required(path: &Path, args: &[&str]) -> String {
        let output =
            Command::new("git").arg("-C").arg(path).args(args).output().expect("git command");
        assert!(
            output.status.success(),
            "git -C {} {:?}\nstderr:\n{}",
            path.display(),
            args,
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8_lossy(&output.stdout).trim().to_string()
    }
}
