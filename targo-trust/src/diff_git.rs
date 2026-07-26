// Developer-only Git-aware source-contract audit diff between refs.
//
// Uses `git show <ref>:<path>` to read file contents at each ref without
// requiring checkout. Runs lightweight source analysis on both versions
// and reports function-level source-inventory changes without claiming proof.
//
// Part of #625: targo trust diff -- show source-contract delta between refs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path};
use std::process::{Command, Output};
use std::time::Duration;

use serde::Serialize;

use crate::bounded_process;
use crate::source_analysis::{self, ParsedFunction, SourceAnalysisSummary, StandaloneOutcome};

const MAX_GIT_METADATA_STREAM_BYTES: usize = 64 * 1024 * 1024;
const MAX_GIT_SOURCE_BYTES: usize = 128 * 1024 * 1024;
const GIT_METADATA_TIMEOUT: Duration = Duration::from_secs(120);
const GIT_SOURCE_TIMEOUT: Duration = Duration::from_secs(30);
const MAX_GIT_ARGUMENT_BYTES: usize = 16 * 1024;

// ---------------------------------------------------------------------------
// Git ref range parsing
// ---------------------------------------------------------------------------

/// A pair of git refs to compare.
#[derive(Debug, Clone)]
pub(crate) struct GitRefRange {
    pub(crate) from: String,
    pub(crate) to: String,
}

/// Parse a ref range from CLI arguments.
///
/// Supports:
///   - `main..feature` (double-dot syntax)
///   - `--from main --to feature` (explicit flags, handled by caller)
///   - `HEAD~3` (single ref is paired with `HEAD` by the caller)
pub(crate) fn parse_ref_range(arg: &str) -> Option<GitRefRange> {
    if arg.contains("...") {
        return None;
    }
    if let Some((from, to)) = arg.split_once("..") {
        let from = from.trim();
        let to = to.trim();
        if from.is_empty() || to.is_empty() || to.contains("..") {
            return None;
        }
        Some(GitRefRange { from: from.to_string(), to: to.to_string() })
    } else {
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GitPathChange {
    from_path: Option<String>,
    to_path: Option<String>,
}

// ---------------------------------------------------------------------------
// Git operations
// ---------------------------------------------------------------------------

/// Resolve a git ref to a full commit hash.
pub(crate) fn resolve_ref(git_ref: &str, repo_dir: &Path) -> Result<String, String> {
    validate_git_argument("ref", git_ref)?;
    let commit_ref = format!("{git_ref}^{{commit}}");
    let mut command = Command::new("git");
    command.args(["rev-parse", "--verify", "--end-of-options", &commit_ref]).current_dir(repo_dir);
    let output = git_output(
        &mut command,
        "git ref resolution",
        MAX_GIT_METADATA_STREAM_BYTES,
        GIT_SOURCE_TIMEOUT,
    )?;

    if !output.status.success() {
        let stderr = strict_utf8(&output.stderr, "git ref-resolution stderr")?;
        return Err(format!("unknown git ref `{git_ref}`: {}", stderr.trim()));
    }

    let commit = strict_utf8(&output.stdout, "git ref-resolution stdout")?.trim();
    if !matches!(commit.len(), 40 | 64) || !commit.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!("git resolved `{git_ref}` to malformed object id `{commit}`"));
    }
    Ok(commit.to_ascii_lowercase())
}

/// Get file contents at a specific git ref.
///
/// Uses `git show <ref>:<path>` to avoid checkout.
/// The status-aware inventory only requests paths known to exist at that ref;
/// any read failure is therefore fatal rather than interpreted as absence.
fn git_show_file(git_ref: &str, file_path: &str, repo_dir: &Path) -> Result<String, String> {
    validate_commit_id(git_ref)?;
    validate_repo_path(file_path)?;
    let spec = format!("{git_ref}:{file_path}");
    let mut command = Command::new("git");
    command.args(["show", "--no-ext-diff", "--no-textconv", "--end-of-options", &spec]);
    command.current_dir(repo_dir);
    let output = git_output(
        &mut command,
        &format!("git source read for `{file_path}`"),
        MAX_GIT_SOURCE_BYTES,
        GIT_SOURCE_TIMEOUT,
    )?;
    if !output.status.success() {
        let stderr = strict_utf8(&output.stderr, "git source-read stderr")?;
        return Err(format!("git could not read `{file_path}` at `{git_ref}`: {}", stderr.trim()));
    }
    strict_utf8(&output.stdout, &format!("source `{file_path}` at `{git_ref}`")).map(str::to_owned)
}

/// List Rust source changes between two resolved commits without losing
/// additions, deletions, copies, or rename endpoints.
fn changed_rs_files(
    from_ref: &str,
    to_ref: &str,
    repo_dir: &Path,
) -> Result<Vec<GitPathChange>, String> {
    validate_commit_id(from_ref)?;
    validate_commit_id(to_ref)?;
    let mut command = Command::new("git");
    command.args([
        "diff",
        "--name-status",
        "-z",
        "--find-renames",
        "--find-copies",
        "--diff-filter=ACMRDT",
        from_ref,
        to_ref,
        "--",
        "*.rs",
    ]);
    command.current_dir(repo_dir);
    let output = git_output(
        &mut command,
        "git Rust-source change inventory",
        MAX_GIT_METADATA_STREAM_BYTES,
        GIT_METADATA_TIMEOUT,
    )?;
    if !output.status.success() {
        let stderr = strict_utf8(&output.stderr, "git diff stderr")?;
        return Err(format!("git source change inventory failed: {}", stderr.trim()));
    }
    parse_name_status_z(&output.stdout)
}

fn git_output(
    command: &mut Command,
    context: &str,
    max_stream_bytes: usize,
    timeout: Duration,
) -> Result<Output, String> {
    bounded_process::output(command, context, max_stream_bytes, timeout)
}

fn strict_utf8<'a>(bytes: &'a [u8], context: &str) -> Result<&'a str, String> {
    std::str::from_utf8(bytes).map_err(|error| format!("{context} is not UTF-8: {error}"))
}

fn validate_git_argument(kind: &str, value: &str) -> Result<(), String> {
    if value.is_empty() {
        return Err(format!("git {kind} must not be empty"));
    }
    if value.len() > MAX_GIT_ARGUMENT_BYTES {
        return Err(format!("git {kind} exceeds the {MAX_GIT_ARGUMENT_BYTES}-byte limit"));
    }
    if value.chars().any(char::is_control) {
        return Err(format!("git {kind} contains a control character"));
    }
    Ok(())
}

fn validate_commit_id(commit: &str) -> Result<(), String> {
    if matches!(commit.len(), 40 | 64) && commit.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        Ok(())
    } else {
        Err("internal git commit id is not a canonical SHA-1/SHA-256 hex digest".to_string())
    }
}

fn validate_repo_path(path: &str) -> Result<(), String> {
    validate_git_argument("path", path)?;
    let path = Path::new(path);
    if path.is_absolute()
        || !path.components().all(|component| matches!(component, Component::Normal(_)))
    {
        return Err(format!(
            "git path is not canonical and repository-relative: `{}`",
            path.display()
        ));
    }
    Ok(())
}

fn parse_name_status_z(bytes: &[u8]) -> Result<Vec<GitPathChange>, String> {
    let mut fields = bytes.split(|byte| *byte == 0).peekable();
    let mut changes = Vec::new();
    let mut seen = BTreeSet::new();
    while let Some(status) = fields.next() {
        if status.is_empty() {
            if fields.peek().is_some() {
                return Err("git name-status output contains an empty interior field".to_string());
            }
            break;
        }
        let status = strict_utf8(status, "git name-status code")?;
        let kind = status.as_bytes()[0];
        if matches!(kind, b'A' | b'D' | b'M') && status.len() != 1 {
            return Err(format!("git name-status code is malformed: `{status}`"));
        }
        let first = fields
            .next()
            .ok_or_else(|| format!("git name-status `{status}` is missing its path"))?;
        let first = strict_utf8(first, "git changed path")?.to_string();
        validate_repo_path(&first)?;
        let change = match kind {
            b'A' => GitPathChange { from_path: None, to_path: Some(first) },
            b'D' => GitPathChange { from_path: Some(first), to_path: None },
            b'M' => GitPathChange { from_path: Some(first.clone()), to_path: Some(first) },
            b'R' | b'C' => {
                if status.len() == 1 || !status[1..].bytes().all(|byte| byte.is_ascii_digit()) {
                    return Err(format!("git rename/copy status is malformed: `{status}`"));
                }
                let score = status[1..]
                    .parse::<u16>()
                    .map_err(|_| format!("git rename/copy score is malformed: `{status}`"))?;
                if score > 100 {
                    return Err(format!("git rename/copy score exceeds 100: `{status}`"));
                }
                let second = fields.next().ok_or_else(|| {
                    format!("git name-status `{status}` is missing its destination path")
                })?;
                let second = strict_utf8(second, "git rename destination")?.to_string();
                validate_repo_path(&second)?;
                GitPathChange { from_path: Some(first), to_path: Some(second) }
            }
            _ => return Err(format!("unsupported git name-status code `{status}`")),
        };
        if !seen.insert((change.from_path.clone(), change.to_path.clone())) {
            return Err(format!("git change inventory contains a duplicate row: {change:?}"));
        }
        changes.push(change);
    }
    Ok(changes)
}

// ---------------------------------------------------------------------------
// Function-level diff
// ---------------------------------------------------------------------------

/// A function's source-audit state at a single git ref.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct FunctionState {
    pub(crate) name: String,
    pub(crate) file: String,
    pub(crate) is_public: bool,
    pub(crate) is_unsafe: bool,
    pub(crate) has_requires: bool,
    pub(crate) has_ensures: bool,
}

impl TryFrom<&ParsedFunction> for FunctionState {
    type Error = String;

    fn try_from(f: &ParsedFunction) -> Result<Self, Self::Error> {
        let file = f
            .file
            .to_str()
            .ok_or_else(|| "source function path is not UTF-8".to_string())?
            .to_string();
        Ok(Self {
            name: f.name.clone(),
            file,
            is_public: f.is_public,
            is_unsafe: f.is_unsafe,
            has_requires: f.has_requires,
            has_ensures: f.has_ensures,
        })
    }
}

/// How a function's source-audit state changed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) enum FunctionChange {
    /// Function was added.
    Added,
    /// Function was removed.
    Removed,
    /// Function gained a spec (requires or ensures).
    GainedSpec,
    /// Function lost a spec.
    LostSpec,
    /// Function changed from safe to unsafe or vice versa.
    SafetyChanged,
    /// Function visibility changed.
    VisibilityChanged,
}

/// A single function-level diff entry.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct FunctionDiffEntry {
    pub(crate) function: String,
    pub(crate) file: String,
    pub(crate) change: FunctionChange,
    pub(crate) detail: String,
    pub(crate) from_state: Option<FunctionState>,
    pub(crate) to_state: Option<FunctionState>,
}

/// Full git-aware diff report.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct GitDiffReport {
    pub(crate) schema_version: &'static str,
    pub(crate) mode: &'static str,
    pub(crate) execution_scope: &'static str,
    pub(crate) proof_authority: &'static str,
    pub(crate) compiler_verification_performed: bool,
    pub(crate) from_ref: String,
    pub(crate) to_ref: String,
    pub(crate) from_commit: String,
    pub(crate) to_commit: String,
    pub(crate) files_changed: usize,
    pub(crate) files_deleted: usize,
    pub(crate) from_summary: DiffSummaryStats,
    pub(crate) to_summary: DiffSummaryStats,
    pub(crate) functions_added: usize,
    pub(crate) functions_removed: usize,
    pub(crate) specs_gained: usize,
    pub(crate) specs_lost: usize,
    pub(crate) safety_changes: usize,
    pub(crate) entries: Vec<FunctionDiffEntry>,
}

/// Summary statistics from source analysis at a ref.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct DiffSummaryStats {
    pub(crate) functions: usize,
    pub(crate) public_functions: usize,
    pub(crate) unsafe_functions: usize,
    pub(crate) specified_functions: usize,
    pub(crate) total_audit_rows: usize,
    pub(crate) present: usize,
    pub(crate) unknown: usize,
}

impl From<&SourceAnalysisSummary> for DiffSummaryStats {
    fn from(s: &SourceAnalysisSummary) -> Self {
        Self {
            functions: s.functions_found,
            public_functions: s.public_functions,
            unsafe_functions: s.unsafe_functions,
            specified_functions: s.specified_functions,
            total_audit_rows: s.total_audit_rows,
            present: s.present,
            unknown: s.unknown,
        }
    }
}

// ---------------------------------------------------------------------------
// Core diff computation
// ---------------------------------------------------------------------------

fn index_functions(
    file_path: &str,
    functions: Vec<ParsedFunction>,
    index: &mut BTreeMap<String, ParsedFunction>,
    all_functions: &mut Vec<ParsedFunction>,
) -> Result<(), String> {
    let mut name_occurrences = BTreeMap::<String, usize>::new();
    for function in functions {
        let occurrence = name_occurrences.entry(function.name.clone()).or_default();
        let key = format!("{file_path}\0{}\0{occurrence:08}", function.name);
        *occurrence += 1;
        if index.insert(key, function.clone()).is_some() {
            return Err(format!("duplicate source-function identity while indexing `{file_path}`"));
        }
        all_functions.push(function);
    }
    Ok(())
}

/// Run the full git-aware diff between two refs.
///
/// Analyzes changed Rust source files at both refs and produces a
/// function-level diff of source-contract state.
pub(crate) fn run_git_diff(
    range: &GitRefRange,
    repo_dir: &Path,
    scope: Option<&str>,
) -> Result<GitDiffReport, String> {
    // Resolve refs to commit hashes.
    let from_commit = resolve_ref(&range.from, repo_dir)?;
    let to_commit = resolve_ref(&range.to, repo_dir)?;

    eprintln!(
        "targo trust: diff {} ({}) .. {} ({})",
        range.from,
        &from_commit[..8.min(from_commit.len())],
        range.to,
        &to_commit[..8.min(to_commit.len())],
    );

    // Find changed files with exact old/new endpoints. Errors are fatal: a
    // failed Git inventory must never become a vacuous zero-change report.
    let mut changes = changed_rs_files(&from_commit, &to_commit, repo_dir)?;
    if let Some(scope) = scope {
        validate_repo_path(scope.trim_end_matches('/'))?;
        let scope = Path::new(scope);
        changes.retain(|change| {
            change
                .from_path
                .as_deref()
                .into_iter()
                .chain(change.to_path.as_deref())
                .any(|path| Path::new(path).starts_with(scope))
        });
    }
    let files_changed = changes.iter().filter(|change| change.to_path.is_some()).count();
    let files_deleted = changes.iter().filter(|change| change.to_path.is_none()).count();

    eprintln!("targo trust: {files_changed} files changed, {files_deleted} files deleted");

    // Analyze functions at both refs for changed files.
    let mut from_functions: BTreeMap<String, ParsedFunction> = BTreeMap::new();
    let mut to_functions: BTreeMap<String, ParsedFunction> = BTreeMap::new();

    let mut from_all_funcs: Vec<ParsedFunction> = Vec::new();
    let mut to_all_funcs: Vec<ParsedFunction> = Vec::new();

    let from_paths: BTreeSet<&str> =
        changes.iter().filter_map(|change| change.from_path.as_deref()).collect();
    let to_paths: BTreeSet<&str> =
        changes.iter().filter_map(|change| change.to_path.as_deref()).collect();
    for file_path in from_paths {
        let content = git_show_file(&from_commit, file_path, repo_dir)?;
        let funcs = source_analysis::extract_functions_from_source(&content, Path::new(file_path));
        index_functions(file_path, funcs, &mut from_functions, &mut from_all_funcs)?;
    }
    for file_path in to_paths {
        let content = git_show_file(&to_commit, file_path, repo_dir)?;
        let funcs = source_analysis::extract_functions_from_source(&content, Path::new(file_path));
        index_functions(file_path, funcs, &mut to_functions, &mut to_all_funcs)?;
    }

    // Compute function-level diff.
    let mut entries = Vec::new();
    let mut functions_added = 0usize;
    let mut functions_removed = 0usize;
    let mut specs_gained = 0usize;
    let mut specs_lost = 0usize;
    let mut safety_changes = 0usize;

    // Check all functions in to-ref: new or changed?
    for (key, to_func) in &to_functions {
        match from_functions.get(key) {
            None => {
                // New function.
                functions_added += 1;
                let detail = if to_func.has_requires || to_func.has_ensures {
                    "new function with specifications".to_string()
                } else if to_func.is_unsafe {
                    "new unsafe function".to_string()
                } else if to_func.is_public {
                    "new public function (no specs)".to_string()
                } else {
                    "new private function".to_string()
                };
                entries.push(FunctionDiffEntry {
                    function: to_func.name.clone(),
                    file: key.split('\0').next().expect("indexed key has a path").to_string(),
                    change: FunctionChange::Added,
                    detail,
                    from_state: None,
                    to_state: Some(FunctionState::try_from(to_func)?),
                });
            }
            Some(from_func) => {
                // Existing function -- check for changes.
                let gained_spec = (!from_func.has_requires && to_func.has_requires)
                    || (!from_func.has_ensures && to_func.has_ensures);
                let lost_spec = (from_func.has_requires && !to_func.has_requires)
                    || (from_func.has_ensures && !to_func.has_ensures);
                let safety_changed = from_func.is_unsafe != to_func.is_unsafe;
                let vis_changed = from_func.is_public != to_func.is_public;

                if gained_spec {
                    specs_gained += 1;
                    let mut parts = Vec::new();
                    if !from_func.has_requires && to_func.has_requires {
                        parts.push("requires spec added");
                    }
                    if !from_func.has_ensures && to_func.has_ensures {
                        parts.push("ensures spec added");
                    }
                    entries.push(FunctionDiffEntry {
                        function: to_func.name.clone(),
                        file: key.split('\0').next().expect("indexed key has a path").to_string(),
                        change: FunctionChange::GainedSpec,
                        detail: parts.join(", "),
                        from_state: Some(FunctionState::try_from(from_func)?),
                        to_state: Some(FunctionState::try_from(to_func)?),
                    });
                }

                if lost_spec {
                    specs_lost += 1;
                    let mut parts = Vec::new();
                    if from_func.has_requires && !to_func.has_requires {
                        parts.push("requires spec removed");
                    }
                    if from_func.has_ensures && !to_func.has_ensures {
                        parts.push("ensures spec removed");
                    }
                    entries.push(FunctionDiffEntry {
                        function: to_func.name.clone(),
                        file: key.split('\0').next().expect("indexed key has a path").to_string(),
                        change: FunctionChange::LostSpec,
                        detail: parts.join(", "),
                        from_state: Some(FunctionState::try_from(from_func)?),
                        to_state: Some(FunctionState::try_from(to_func)?),
                    });
                }

                if safety_changed {
                    safety_changes += 1;
                    let detail = if to_func.is_unsafe {
                        "became unsafe".to_string()
                    } else {
                        "became safe".to_string()
                    };
                    entries.push(FunctionDiffEntry {
                        function: to_func.name.clone(),
                        file: key.split('\0').next().expect("indexed key has a path").to_string(),
                        change: FunctionChange::SafetyChanged,
                        detail,
                        from_state: Some(FunctionState::try_from(from_func)?),
                        to_state: Some(FunctionState::try_from(to_func)?),
                    });
                }

                if vis_changed && !gained_spec && !lost_spec && !safety_changed {
                    let detail = if to_func.is_public {
                        "became public".to_string()
                    } else {
                        "became private".to_string()
                    };
                    entries.push(FunctionDiffEntry {
                        function: to_func.name.clone(),
                        file: key.split('\0').next().expect("indexed key has a path").to_string(),
                        change: FunctionChange::VisibilityChanged,
                        detail,
                        from_state: Some(FunctionState::try_from(from_func)?),
                        to_state: Some(FunctionState::try_from(to_func)?),
                    });
                }
            }
        }
    }

    // Check for removed functions.
    for (key, from_func) in &from_functions {
        if !to_functions.contains_key(key) {
            functions_removed += 1;
            let detail = if from_func.has_requires || from_func.has_ensures {
                "removed function (had specifications)".to_string()
            } else {
                "removed function".to_string()
            };
            entries.push(FunctionDiffEntry {
                function: from_func.name.clone(),
                file: key.split('\0').next().expect("indexed key has a path").to_string(),
                change: FunctionChange::Removed,
                detail,
                from_state: Some(FunctionState::try_from(from_func)?),
                to_state: None,
            });
        }
    }

    // Sort entries: regressions first (lost specs, safety changes, removed),
    // then improvements (gained specs, added).
    entries.sort_by(|a, b| {
        fn change_priority(c: FunctionChange) -> u8 {
            match c {
                FunctionChange::LostSpec => 0,
                FunctionChange::SafetyChanged => 1,
                FunctionChange::Removed => 2,
                FunctionChange::GainedSpec => 3,
                FunctionChange::Added => 4,
                FunctionChange::VisibilityChanged => 5,
            }
        }
        change_priority(a.change)
            .cmp(&change_priority(b.change))
            .then_with(|| a.file.cmp(&b.file))
            .then_with(|| a.function.cmp(&b.function))
    });

    // Build summary stats.
    let from_vcs = source_analysis::generate_standalone_vcs(&from_all_funcs);
    let to_vcs = source_analysis::generate_standalone_vcs(&to_all_funcs);

    let from_summary = DiffSummaryStats {
        functions: from_all_funcs.len(),
        public_functions: from_all_funcs.iter().filter(|f| f.is_public).count(),
        unsafe_functions: from_all_funcs.iter().filter(|f| f.is_unsafe).count(),
        specified_functions: from_all_funcs
            .iter()
            .filter(|f| f.has_requires || f.has_ensures)
            .count(),
        total_audit_rows: from_vcs.len(),
        present: from_vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Present).count(),
        unknown: from_vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Unknown).count(),
    };

    let to_summary = DiffSummaryStats {
        functions: to_all_funcs.len(),
        public_functions: to_all_funcs.iter().filter(|f| f.is_public).count(),
        unsafe_functions: to_all_funcs.iter().filter(|f| f.is_unsafe).count(),
        specified_functions: to_all_funcs
            .iter()
            .filter(|f| f.has_requires || f.has_ensures)
            .count(),
        total_audit_rows: to_vcs.len(),
        present: to_vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Present).count(),
        unknown: to_vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Unknown).count(),
    };

    Ok(GitDiffReport {
        schema_version: "trust.source-diff-audit.v1",
        mode: "source-diff-audit",
        execution_scope: "developer-only",
        proof_authority: "none",
        compiler_verification_performed: false,
        from_ref: range.from.clone(),
        to_ref: range.to.clone(),
        from_commit,
        to_commit,
        files_changed,
        files_deleted,
        from_summary,
        to_summary,
        functions_added,
        functions_removed,
        specs_gained,
        specs_lost,
        safety_changes,
        entries,
    })
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

impl GitDiffReport {
    pub(crate) fn render_terminal(&self) {
        eprintln!();
        eprintln!("=== Trust Non-Proof Source-Contract Diff ===");
        eprintln!(
            "  Scope: DEVELOPER-ONLY | Proof authority: NONE | Compiler verification: NOT RUN"
        );
        eprintln!(
            "  {} ({}) .. {} ({})",
            self.from_ref,
            &self.from_commit[..8.min(self.from_commit.len())],
            self.to_ref,
            &self.to_commit[..8.min(self.to_commit.len())],
        );
        eprintln!("  {} files changed, {} files deleted", self.files_changed, self.files_deleted);
        eprintln!();

        // Summary table.
        eprintln!("  {:>20}  {:>8}  {:>8}", "", &self.from_ref, &self.to_ref);
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "Functions", self.from_summary.functions, self.to_summary.functions,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "Public", self.from_summary.public_functions, self.to_summary.public_functions,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "Unsafe", self.from_summary.unsafe_functions, self.to_summary.unsafe_functions,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "With specs",
            self.from_summary.specified_functions,
            self.to_summary.specified_functions,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "Source facts", self.from_summary.present, self.to_summary.present,
        );
        eprintln!(
            "  {:>20}  {:>8}  {:>8}",
            "Audit unknown", self.from_summary.unknown, self.to_summary.unknown,
        );
        eprintln!();

        // Individual changes.
        if self.entries.is_empty() {
            eprintln!("  No source-contract-relevant changes.");
        } else {
            for entry in &self.entries {
                let icon = match entry.change {
                    FunctionChange::GainedSpec | FunctionChange::Added => "+",
                    FunctionChange::LostSpec | FunctionChange::Removed => "-",
                    FunctionChange::SafetyChanged => "!",
                    FunctionChange::VisibilityChanged => "~",
                };
                eprintln!("  [{icon}] {}::{} -- {}", entry.file, entry.function, entry.detail);
            }
        }

        eprintln!();

        // Delta summary.
        let delta_specs = self.to_summary.specified_functions as i64
            - self.from_summary.specified_functions as i64;
        let delta_present = self.to_summary.present as i64 - self.from_summary.present as i64;
        let delta_unsafe =
            self.to_summary.unsafe_functions as i64 - self.from_summary.unsafe_functions as i64;

        eprintln!(
            "Delta: specs {:+}, source facts {:+}, unsafe {:+}",
            delta_specs, delta_present, delta_unsafe
        );
        eprintln!(
            "Summary: {} added, {} removed, {} gained specs, {} lost specs, {} safety changes",
            self.functions_added,
            self.functions_removed,
            self.specs_gained,
            self.specs_lost,
            self.safety_changes,
        );

        // Verdict.
        if self.has_regressions() {
            eprintln!("Audit result: REGRESSIONS DETECTED (non-proof)");
        } else if self.has_improvements() {
            eprintln!("Audit result: IMPROVED (non-proof)");
        } else {
            eprintln!("Audit result: NO CHANGE (non-proof)");
        }
        eprintln!("===============================");
    }

    pub(crate) fn render_json(&self) {
        match serde_json::to_string_pretty(self) {
            Ok(json) => println!("{json}"),
            Err(e) => eprintln!("targo trust: failed to serialize git diff: {e}"),
        }
    }

    /// Returns true if the diff contains regressions (lost specs, removed
    /// specified functions, or functions that became unsafe).
    pub(crate) fn has_regressions(&self) -> bool {
        self.specs_lost > 0
            || self.entries.iter().any(|e| {
                e.change == FunctionChange::Removed
                    && e.from_state.as_ref().is_some_and(|s| s.has_requires || s.has_ensures)
            })
            || self.entries.iter().any(|e| {
                e.change == FunctionChange::SafetyChanged
                    && e.to_state.as_ref().is_some_and(|s| s.is_unsafe)
            })
    }

    /// Returns true if the diff contains improvements.
    pub(crate) fn has_improvements(&self) -> bool {
        self.specs_gained > 0
            || self.entries.iter().any(|e| {
                e.change == FunctionChange::SafetyChanged
                    && e.to_state.as_ref().is_some_and(|s| !s.is_unsafe)
            })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn test_parse_ref_range_double_dot() {
        let range = parse_ref_range("main..feature").expect("should parse");
        assert_eq!(range.from, "main");
        assert_eq!(range.to, "feature");
    }

    #[test]
    fn test_parse_ref_range_with_slashes() {
        let range = parse_ref_range("origin/main..HEAD").expect("should parse");
        assert_eq!(range.from, "origin/main");
        assert_eq!(range.to, "HEAD");
    }

    #[test]
    fn test_parse_ref_range_with_tilde() {
        let range = parse_ref_range("HEAD~5..HEAD").expect("should parse");
        assert_eq!(range.from, "HEAD~5");
        assert_eq!(range.to, "HEAD");
    }

    #[test]
    fn test_parse_ref_range_empty_from() {
        assert!(parse_ref_range("..HEAD").is_none());
    }

    #[test]
    fn test_parse_ref_range_empty_to() {
        assert!(parse_ref_range("main..").is_none());
    }

    #[test]
    fn test_parse_ref_range_no_dots() {
        assert!(parse_ref_range("main").is_none());
    }

    #[test]
    fn test_parse_ref_range_rejects_triple_or_multiple_ranges() {
        assert!(parse_ref_range("main...feature").is_none());
        assert!(parse_ref_range("main..middle..feature").is_none());
    }

    #[test]
    fn test_parse_ref_range_commit_hashes() {
        let range = parse_ref_range("abc123..def456").expect("should parse");
        assert_eq!(range.from, "abc123");
        assert_eq!(range.to, "def456");
    }

    #[test]
    fn name_status_transport_preserves_add_delete_modify_rename_and_copy() {
        let bytes = b"M\0src/modified.rs\0A\0src/added.rs\0D\0src/deleted.rs\0R100\0src/old.rs\0src/new.rs\0C075\0src/source.rs\0src/copy.rs\0";
        let changes = parse_name_status_z(bytes).expect("valid NUL-delimited Git inventory");
        assert_eq!(
            changes,
            vec![
                GitPathChange {
                    from_path: Some("src/modified.rs".into()),
                    to_path: Some("src/modified.rs".into()),
                },
                GitPathChange { from_path: None, to_path: Some("src/added.rs".into()) },
                GitPathChange { from_path: Some("src/deleted.rs".into()), to_path: None },
                GitPathChange {
                    from_path: Some("src/old.rs".into()),
                    to_path: Some("src/new.rs".into()),
                },
                GitPathChange {
                    from_path: Some("src/source.rs".into()),
                    to_path: Some("src/copy.rs".into()),
                },
            ]
        );
    }

    #[test]
    fn name_status_transport_rejects_ambiguous_or_unsafe_rows() {
        for bytes in [
            b"M\0../escape.rs\0".as_slice(),
            b"M\0src/line\nbreak.rs\0".as_slice(),
            b"R100\0src/old.rs\0".as_slice(),
            b"R101\0src/old.rs\0src/new.rs\0".as_slice(),
            b"A9\0src/added.rs\0".as_slice(),
            b"T\0src/type-change.rs\0".as_slice(),
            b"M\0src/same.rs\0M\0src/same.rs\0".as_slice(),
            b"M\0src/ok.rs\0\0A\0src/hidden.rs\0".as_slice(),
        ] {
            assert!(parse_name_status_z(bytes).is_err(), "accepted unsafe row: {bytes:?}");
        }
        assert!(parse_name_status_z(b"M\0src/\xff.rs\0").is_err());
    }

    #[test]
    fn option_like_ref_is_data_and_control_ref_is_rejected() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("repository root");
        let error = resolve_ref("--help", repo).expect_err("option-like text is not a valid ref");
        assert!(error.contains("unknown git ref `--help`"), "{error}");
        assert!(resolve_ref("HEAD\nmalicious", repo).is_err());
    }

    #[test]
    fn duplicate_function_names_receive_distinct_source_identities() {
        let source = "fn same() {}\nfn same() {}\n";
        let functions =
            source_analysis::extract_functions_from_source(source, Path::new("src/lib.rs"));
        let mut index = BTreeMap::new();
        let mut all = Vec::new();
        index_functions("src/lib.rs", functions, &mut index, &mut all)
            .expect("duplicate names are indexed by occurrence");
        assert_eq!(index.len(), 2);
        assert_eq!(all.len(), 2);
    }

    #[test]
    fn test_function_state_from_parsed() {
        let func = ParsedFunction {
            name: "test_fn".into(),
            file: PathBuf::from("src/lib.rs"),
            line: 10,
            is_public: true,
            is_unsafe: false,
            has_requires: true,
            has_ensures: false,
            return_type: Some("i32".into()),
            params: vec!["x".into()],
            typed_params: vec![],
        };
        let state = FunctionState::try_from(&func).expect("UTF-8 fixture path");
        assert_eq!(state.name, "test_fn");
        assert!(state.is_public);
        assert!(state.has_requires);
        assert!(!state.has_ensures);
    }

    #[cfg(unix)]
    #[test]
    fn function_state_rejects_non_utf8_source_identity() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt;

        let func = ParsedFunction {
            name: "test_fn".into(),
            file: PathBuf::from(OsString::from_vec(b"src/\xff.rs".to_vec())),
            line: 1,
            is_public: false,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: None,
            params: Vec::new(),
            typed_params: Vec::new(),
        };
        assert!(FunctionState::try_from(&func).is_err());
    }

    #[test]
    fn test_git_diff_report_has_regressions() {
        let report = GitDiffReport {
            schema_version: "trust.source-diff-audit.v1",
            mode: "source-diff-audit",
            execution_scope: "developer-only",
            proof_authority: "none",
            compiler_verification_performed: false,
            from_ref: "main".into(),
            to_ref: "feature".into(),
            from_commit: "abc".into(),
            to_commit: "def".into(),
            files_changed: 1,
            files_deleted: 0,
            from_summary: DiffSummaryStats {
                functions: 1,
                public_functions: 1,
                unsafe_functions: 0,
                specified_functions: 1,
                total_audit_rows: 1,
                present: 1,
                unknown: 0,
            },
            to_summary: DiffSummaryStats {
                functions: 1,
                public_functions: 1,
                unsafe_functions: 0,
                specified_functions: 0,
                total_audit_rows: 0,
                present: 0,
                unknown: 0,
            },
            functions_added: 0,
            functions_removed: 0,
            specs_gained: 0,
            specs_lost: 1,
            safety_changes: 0,
            entries: vec![FunctionDiffEntry {
                function: "foo".into(),
                file: "src/lib.rs".into(),
                change: FunctionChange::LostSpec,
                detail: "requires spec removed".into(),
                from_state: Some(FunctionState {
                    name: "foo".into(),
                    file: "src/lib.rs".into(),
                    is_public: true,
                    is_unsafe: false,
                    has_requires: true,
                    has_ensures: false,
                }),
                to_state: Some(FunctionState {
                    name: "foo".into(),
                    file: "src/lib.rs".into(),
                    is_public: true,
                    is_unsafe: false,
                    has_requires: false,
                    has_ensures: false,
                }),
            }],
        };
        assert!(report.has_regressions());
        assert!(!report.has_improvements());
    }

    #[test]
    fn test_git_diff_report_has_improvements() {
        let report = GitDiffReport {
            schema_version: "trust.source-diff-audit.v1",
            mode: "source-diff-audit",
            execution_scope: "developer-only",
            proof_authority: "none",
            compiler_verification_performed: false,
            from_ref: "main".into(),
            to_ref: "feature".into(),
            from_commit: "abc".into(),
            to_commit: "def".into(),
            files_changed: 1,
            files_deleted: 0,
            from_summary: DiffSummaryStats {
                functions: 1,
                public_functions: 1,
                unsafe_functions: 0,
                specified_functions: 0,
                total_audit_rows: 0,
                present: 0,
                unknown: 0,
            },
            to_summary: DiffSummaryStats {
                functions: 1,
                public_functions: 1,
                unsafe_functions: 0,
                specified_functions: 1,
                total_audit_rows: 1,
                present: 1,
                unknown: 0,
            },
            functions_added: 0,
            functions_removed: 0,
            specs_gained: 1,
            specs_lost: 0,
            safety_changes: 0,
            entries: vec![FunctionDiffEntry {
                function: "foo".into(),
                file: "src/lib.rs".into(),
                change: FunctionChange::GainedSpec,
                detail: "ensures spec added".into(),
                from_state: None,
                to_state: None,
            }],
        };
        assert!(!report.has_regressions());
        assert!(report.has_improvements());
    }

    #[test]
    fn test_git_diff_report_no_changes() {
        let report = GitDiffReport {
            schema_version: "trust.source-diff-audit.v1",
            mode: "source-diff-audit",
            execution_scope: "developer-only",
            proof_authority: "none",
            compiler_verification_performed: false,
            from_ref: "main".into(),
            to_ref: "feature".into(),
            from_commit: "abc".into(),
            to_commit: "def".into(),
            files_changed: 0,
            files_deleted: 0,
            from_summary: DiffSummaryStats {
                functions: 0,
                public_functions: 0,
                unsafe_functions: 0,
                specified_functions: 0,
                total_audit_rows: 0,
                present: 0,
                unknown: 0,
            },
            to_summary: DiffSummaryStats {
                functions: 0,
                public_functions: 0,
                unsafe_functions: 0,
                specified_functions: 0,
                total_audit_rows: 0,
                present: 0,
                unknown: 0,
            },
            functions_added: 0,
            functions_removed: 0,
            specs_gained: 0,
            specs_lost: 0,
            safety_changes: 0,
            entries: vec![],
        };
        assert!(!report.has_regressions());
        assert!(!report.has_improvements());
    }

    #[test]
    fn test_git_diff_report_json_serialization() {
        let report = GitDiffReport {
            schema_version: "trust.source-diff-audit.v1",
            mode: "source-diff-audit",
            execution_scope: "developer-only",
            proof_authority: "none",
            compiler_verification_performed: false,
            from_ref: "main".into(),
            to_ref: "HEAD".into(),
            from_commit: "abc123".into(),
            to_commit: "def456".into(),
            files_changed: 2,
            files_deleted: 1,
            from_summary: DiffSummaryStats {
                functions: 5,
                public_functions: 3,
                unsafe_functions: 1,
                specified_functions: 2,
                total_audit_rows: 4,
                present: 2,
                unknown: 2,
            },
            to_summary: DiffSummaryStats {
                functions: 6,
                public_functions: 4,
                unsafe_functions: 0,
                specified_functions: 3,
                total_audit_rows: 5,
                present: 3,
                unknown: 2,
            },
            functions_added: 2,
            functions_removed: 1,
            specs_gained: 1,
            specs_lost: 0,
            safety_changes: 1,
            entries: vec![],
        };
        let json = serde_json::to_string(&report).expect("should serialize");
        assert!(json.contains("\"from_ref\":\"main\""));
        assert!(json.contains("\"specs_gained\":1"));
        assert!(json.contains("\"proof_authority\":\"none\""));
        assert!(json.contains("\"execution_scope\":\"developer-only\""));
        assert!(json.contains("\"compiler_verification_performed\":false"));
        assert!(!json.contains("\"proved\""));
    }
}
