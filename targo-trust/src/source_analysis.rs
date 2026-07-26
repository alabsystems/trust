// Lightweight non-proof source audit for explicit standalone mode.
//
// Parses Rust source files to extract function signatures, native contract
// clauses, and upstream-compatibility attributes without requiring the full
// compiler pipeline. Generates conservative audit rows for each function.
//
// This enables `targo trust check --standalone` to produce a clearly labeled
// non-proof inventory when the Trust compiler is intentionally not invoked.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::input_limits::{
    MAX_RELEASE_METADATA_BYTES, MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_utf8_file,
};

// ---------------------------------------------------------------------------
// Parsed source types
// ---------------------------------------------------------------------------

/// A function extracted from source-level parsing.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ParsedFunction {
    pub(crate) name: String,
    pub(crate) file: PathBuf,
    pub(crate) line: usize,
    pub(crate) is_public: bool,
    pub(crate) is_unsafe: bool,
    pub(crate) has_requires: bool,
    pub(crate) has_ensures: bool,
    pub(crate) return_type: Option<String>,
    pub(crate) params: Vec<String>,
    /// Parameters with types: (name, type_string). Used by `targo trust init`.
    pub(crate) typed_params: Vec<(String, String)>,
}

/// A source-audit row generated without compiler or proof authority.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct StandaloneVc {
    pub(crate) function: String,
    pub(crate) file: PathBuf,
    pub(crate) kind: VcKind,
    pub(crate) description: String,
    pub(crate) outcome: StandaloneOutcome,
}

/// Kind of audit row for source-level analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub(crate) enum VcKind {
    /// Function has a native or compatibility `requires` specification.
    PreconditionPresent,
    /// Function has a native or compatibility `ensures` specification.
    PostconditionPresent,
    /// Unsafe function detected -- needs safety audit.
    UnsafeFunction,
    /// Public function without specification.
    UnspecifiedPublicApi,
    /// Hardened profile: raw path API can re-resolve attacker-controlled names.
    HardenedRawPathApi,
    /// Hardened profile: path spelling or canonicalization is not stable file identity.
    HardenedPathIdentity,
    /// Hardened profile: path-based permission change needs identity and state proof.
    HardenedPermissionChange,
    /// Hardened profile: path-based creation needs mode/parent identity proof.
    HardenedPermissionCreate,
    /// Hardened profile: object is created before permissions/owner are fixed.
    HardenedPermissionWindow,
    /// Hardened profile: byte payload may be changed by lossy text conversion.
    HardenedByteLoss,
    /// Hardened profile: Unix boundary bytes may be rejected as invalid UTF-8.
    HardenedUtf8Boundary,
    /// Hardened profile: error value is explicitly discarded or downgraded.
    HardenedErrorDiscard,
    /// Hardened profile: public/untrusted path can terminate through panic.
    HardenedPanic,
    /// Hardened profile: privilege/root/name-service ordering needs a trust-domain proof.
    HardenedTrustBoundary,
    /// Hardened profile: a trust-domain transition is ordered before name-service/loading.
    HardenedTrustDomainOrder,
    /// Hardened profile: observable CLI compatibility must be modeled explicitly.
    HardenedCompatibility,
    /// Hardened profile: process startup/signal semantics affect observable compatibility.
    HardenedProcessSemantics,
    /// Hardened profile: unsafe operation needs an explicit trusted wrapper/certificate.
    HardenedUnsafeOperation,
    /// Hardened profile: FFI boundary needs explicit ABI/memory/trust evidence.
    HardenedFfiBoundary,
}

/// Outcome of a standalone VC -- note this is analysis-level, not solver-level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) enum StandaloneOutcome {
    /// a clause/spec was *detected in source* (for example, native `requires`
    /// / `ensures`). This is presence detection, NOT a
    /// solver discharge — it must never render as `PROVED` or be counted as
    /// proved; it must never render like a discharged compiler obligation.
    Present,
    /// Something needs attention.
    Unknown,
    /// Problem detected.
    Failed,
}

/// Options controlling standalone source analysis.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct SourceAnalysisOptions {
    /// Enable fail-closed hardened checks for OS/path/permissions/bytes/error/
    /// trust-domain/compat/process/unsafe-FFI boundaries.
    pub(crate) hardened: bool,
}

// ---------------------------------------------------------------------------
// Source summary
// ---------------------------------------------------------------------------

/// Summary of standalone source analysis.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct SourceAnalysisSummary {
    pub(crate) files_analyzed: usize,
    pub(crate) functions_found: usize,
    pub(crate) public_functions: usize,
    pub(crate) unsafe_functions: usize,
    pub(crate) specified_functions: usize,
    pub(crate) total_audit_rows: usize,
    /// Count of source facts detected without compiler or proof authority.
    pub(crate) present: usize,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
    pub(crate) functions: Vec<ParsedFunction>,
    #[serde(rename = "audit_rows")]
    pub(crate) vcs: Vec<StandaloneVc>,
}

// ---------------------------------------------------------------------------
// Source file discovery
// ---------------------------------------------------------------------------

/// Cargo manifest fields relevant to standalone target discovery.
#[derive(Debug, Default, Deserialize)]
struct CargoManifest {
    package: Option<ManifestPackage>,
    workspace: Option<ManifestWorkspace>,
    lib: Option<ManifestTarget>,
    #[serde(default)]
    bin: Vec<ManifestNamedTarget>,
    #[serde(default)]
    example: Vec<ManifestNamedTarget>,
    #[serde(default)]
    test: Vec<ManifestNamedTarget>,
    #[serde(default)]
    bench: Vec<ManifestNamedTarget>,
}

#[derive(Debug, Default, Deserialize)]
struct ManifestPackage {
    #[serde(default)]
    autobins: Option<bool>,
    #[serde(default)]
    autoexamples: Option<bool>,
    #[serde(default)]
    autotests: Option<bool>,
    #[serde(default)]
    autobenches: Option<bool>,
}

#[derive(Debug, Default, Deserialize)]
struct ManifestWorkspace {
    #[serde(default)]
    members: Vec<String>,
    #[serde(default, rename = "default-members")]
    default_members: Vec<String>,
    #[serde(default)]
    exclude: Vec<String>,
}

#[derive(Debug, Default, Deserialize)]
struct ManifestTarget {
    path: Option<PathBuf>,
}

#[derive(Debug, Default, Deserialize)]
struct ManifestNamedTarget {
    name: Option<String>,
    path: Option<PathBuf>,
}

/// Find all .rs source files in a crate directory or manifest path.
///
/// Standalone mode prefers Cargo manifest target discovery so it can honor
/// custom target paths, bin layouts, ancestor package roots, workspace member
/// manifests, and explicit manifest-path API calls. If discovery fails, it
/// falls back to scanning `<root>/src` for compatibility.
pub(crate) fn find_source_files(crate_root: &Path) -> Vec<PathBuf> {
    if let Some(manifest_path) = resolve_manifest_path(crate_root) {
        return find_source_files_for_manifest(&manifest_path);
    }
    legacy_src_scan(crate_root)
}

/// Find source files using an explicit Cargo manifest path.
///
/// Relative manifest paths are interpreted relative to `crate_root`; callers
/// that need cwd-relative CLI behavior should resolve that before calling.
#[cfg(test)]
pub(crate) fn find_source_files_with_manifest_path(
    crate_root: &Path,
    manifest_path: &Path,
) -> Vec<PathBuf> {
    let manifest_path = if manifest_path.is_absolute() {
        manifest_path.to_path_buf()
    } else {
        crate_root.join(manifest_path)
    };
    find_source_files_for_manifest(&manifest_path)
}

fn find_source_files_for_manifest(manifest_path: &Path) -> Vec<PathBuf> {
    let mut visited = BTreeSet::new();
    let manifest_files = collect_manifest_source_files(manifest_path, &mut visited);
    if !manifest_files.is_empty() {
        return manifest_files;
    }
    if let Some(manifest_dir) = manifest_path.parent() {
        return legacy_src_scan(manifest_dir);
    }
    Vec::new()
}

fn legacy_src_scan(crate_root: &Path) -> Vec<PathBuf> {
    let src_dir = crate_root.join("src");
    if !is_non_symlink_dir(&src_dir) {
        return Vec::new();
    }
    collect_rs_files(&src_dir)
}

fn collect_rs_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(_) => return files,
    };
    for entry in entries {
        let entry = match entry {
            Ok(e) => e,
            Err(_) => continue,
        };
        let path = entry.path();
        if is_non_symlink_dir(&path) {
            files.extend(collect_rs_files(&path));
        } else if is_non_symlink_file(&path) && path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }
    files.sort();
    files
}

fn resolve_manifest_path(crate_root: &Path) -> Option<PathBuf> {
    manifest_path_from_input(crate_root)
}

fn manifest_path_from_input(path: &Path) -> Option<PathBuf> {
    if path.is_file() {
        if path.file_name().is_some_and(|name| name == "Cargo.toml") {
            return Some(path.to_path_buf());
        }
        return path.parent().and_then(find_manifest_in_ancestors);
    }

    find_manifest_in_ancestors(path)
}

fn find_manifest_in_ancestors(dir: &Path) -> Option<PathBuf> {
    dir.ancestors().map(|ancestor| ancestor.join("Cargo.toml")).find(|path| path.is_file())
}

fn collect_manifest_source_files(
    manifest_path: &Path,
    visited_manifests: &mut BTreeSet<PathBuf>,
) -> Vec<PathBuf> {
    let manifest_key = canonicalize_or_self(manifest_path);
    if !visited_manifests.insert(manifest_key) {
        return Vec::new();
    }

    let manifest_dir = manifest_path.parent().unwrap_or_else(|| Path::new("."));
    let content = match read_bounded_utf8_file(manifest_path, MAX_RELEASE_METADATA_BYTES) {
        Ok(content) => content,
        Err(_) => return legacy_src_scan(manifest_dir),
    };
    let manifest = match toml::from_str::<CargoManifest>(&content) {
        Ok(manifest) => manifest,
        Err(_) => return legacy_src_scan(manifest_dir),
    };

    if manifest.package.is_some()
        || manifest.lib.is_some()
        || !manifest.bin.is_empty()
        || !manifest.example.is_empty()
        || !manifest.test.is_empty()
        || !manifest.bench.is_empty()
    {
        return collect_package_target_files(manifest_dir, &manifest);
    }

    if let Some(workspace) = manifest.workspace.as_ref() {
        return collect_workspace_member_files(manifest_dir, workspace, visited_manifests);
    }

    legacy_src_scan(manifest_dir)
}

fn collect_package_target_files(manifest_dir: &Path, manifest: &CargoManifest) -> Vec<PathBuf> {
    let mut files = BTreeSet::new();

    if let Some(lib) = manifest.lib.as_ref() {
        if let Some(path) = lib.path.as_ref() {
            push_target_file(&mut files, manifest_dir, manifest_dir.join(path));
        } else {
            push_target_file(&mut files, manifest_dir, manifest_dir.join("src/lib.rs"));
        }
    } else {
        push_target_file(&mut files, manifest_dir, manifest_dir.join("src/lib.rs"));
    }

    for bin in &manifest.bin {
        if let Some(path) = bin.path.as_ref() {
            push_target_file(&mut files, manifest_dir, manifest_dir.join(path));
        } else if let Some(name) = bin.name.as_deref() {
            push_named_bin_defaults(&mut files, manifest_dir, name);
        }
    }

    push_named_manifest_targets(&mut files, manifest_dir, &manifest.example, "examples");
    push_named_manifest_targets(&mut files, manifest_dir, &manifest.test, "tests");
    push_named_manifest_targets(&mut files, manifest_dir, &manifest.bench, "benches");

    if manifest.package.as_ref().and_then(|package| package.autobins).unwrap_or(true) {
        push_target_file(&mut files, manifest_dir, manifest_dir.join("src/main.rs"));
        push_auto_bin_targets(&mut files, manifest_dir, &manifest_dir.join("src/bin"));
    }
    if manifest.package.as_ref().and_then(|package| package.autoexamples).unwrap_or(true) {
        push_auto_named_targets(&mut files, manifest_dir, "examples", true);
    }
    if manifest.package.as_ref().and_then(|package| package.autotests).unwrap_or(true) {
        push_auto_named_targets(&mut files, manifest_dir, "tests", false);
    }
    if manifest.package.as_ref().and_then(|package| package.autobenches).unwrap_or(true) {
        push_auto_named_targets(&mut files, manifest_dir, "benches", false);
    }

    files.into_iter().collect()
}

fn push_target_file(files: &mut BTreeSet<PathBuf>, manifest_dir: &Path, path: PathBuf) {
    if is_manifest_target_without_symlink_components(manifest_dir, &path) {
        if let Some(parent) = path.parent() {
            files.extend(collect_rs_files(parent));
        } else {
            files.insert(path);
        }
    }
}

fn push_named_bin_defaults(files: &mut BTreeSet<PathBuf>, manifest_dir: &Path, name: &str) {
    push_target_file(files, manifest_dir, manifest_dir.join(format!("src/bin/{name}.rs")));
    push_target_file(files, manifest_dir, manifest_dir.join(format!("src/bin/{name}/main.rs")));
}

fn push_named_manifest_targets(
    files: &mut BTreeSet<PathBuf>,
    manifest_dir: &Path,
    targets: &[ManifestNamedTarget],
    target_dir: &str,
) {
    for target in targets {
        if let Some(path) = target.path.as_ref() {
            push_target_file(files, manifest_dir, manifest_dir.join(path));
        } else if let Some(name) = target.name.as_deref() {
            push_target_file(
                files,
                manifest_dir,
                manifest_dir.join(format!("{target_dir}/{name}.rs")),
            );
            push_target_file(
                files,
                manifest_dir,
                manifest_dir.join(format!("{target_dir}/{name}/main.rs")),
            );
        }
    }
}

fn push_auto_bin_targets(files: &mut BTreeSet<PathBuf>, manifest_dir: &Path, src_bin_dir: &Path) {
    let entries = match std::fs::read_dir(src_bin_dir) {
        Ok(entries) => entries,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if is_non_symlink_file(&path) && path.extension().is_some_and(|ext| ext == "rs") {
            push_target_file(files, manifest_dir, path);
            continue;
        }
        if is_non_symlink_dir(&path) {
            push_target_file(files, manifest_dir, path.join("main.rs"));
        }
    }
}

fn push_auto_named_targets(
    files: &mut BTreeSet<PathBuf>,
    manifest_dir: &Path,
    target_dir: &str,
    include_directory_main: bool,
) {
    let dir = manifest_dir.join(target_dir);
    let entries = match std::fs::read_dir(&dir) {
        Ok(entries) => entries,
        Err(_) => return,
    };

    let mut top_level_target_files = BTreeSet::new();
    for entry in entries.flatten() {
        let path = entry.path();
        if is_non_symlink_file(&path) && path.extension().is_some_and(|ext| ext == "rs") {
            push_target_file(&mut top_level_target_files, manifest_dir, path);
            continue;
        }
        if include_directory_main && is_non_symlink_dir(&path) {
            push_target_file(files, manifest_dir, path.join("main.rs"));
        }
    }

    if !include_directory_main {
        let root = manifest_dir.join(target_dir);
        top_level_target_files.retain(|path| !is_nested_main_file(&root, path));
    }
    files.extend(top_level_target_files);
}

fn is_nested_main_file(root: &Path, path: &Path) -> bool {
    path.file_name().is_some_and(|name| name == "main.rs")
        && path.parent().is_some_and(|parent| parent != root)
}

fn is_manifest_target_without_symlink_components(manifest_dir: &Path, path: &Path) -> bool {
    if !is_non_symlink_file(path) {
        return false;
    }

    let Ok(relative) = path.strip_prefix(manifest_dir) else {
        return false;
    };
    let mut current = manifest_dir.to_path_buf();
    for component in relative.components() {
        match component {
            Component::CurDir => {}
            Component::Normal(part) => {
                current.push(part);
                let Ok(metadata) = std::fs::symlink_metadata(&current) else {
                    return false;
                };
                if metadata.file_type().is_symlink() {
                    return false;
                }
            }
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => return false,
        }
    }

    true
}

fn collect_workspace_member_files(
    workspace_dir: &Path,
    workspace: &ManifestWorkspace,
    visited_manifests: &mut BTreeSet<PathBuf>,
) -> Vec<PathBuf> {
    let member_patterns = if workspace.default_members.is_empty() {
        &workspace.members
    } else {
        &workspace.default_members
    };
    let excluded_manifests: BTreeSet<PathBuf> =
        expand_workspace_member_manifests(workspace_dir, &workspace.exclude)
            .into_iter()
            .map(|manifest| canonicalize_or_self(&manifest))
            .collect();
    let mut files = BTreeSet::new();

    for member_manifest in expand_workspace_member_manifests(workspace_dir, member_patterns) {
        if excluded_manifests.contains(&canonicalize_or_self(&member_manifest)) {
            continue;
        }
        files.extend(collect_manifest_source_files(&member_manifest, visited_manifests));
    }

    files.into_iter().collect()
}

fn expand_workspace_member_manifests(
    workspace_dir: &Path,
    member_patterns: &[String],
) -> Vec<PathBuf> {
    let mut manifests = BTreeSet::new();

    for pattern in member_patterns {
        for member_dir in expand_workspace_member_pattern(workspace_dir, pattern) {
            let manifest_path = if member_dir.file_name().is_some_and(|name| name == "Cargo.toml") {
                member_dir
            } else {
                member_dir.join("Cargo.toml")
            };
            if is_non_symlink_file(&manifest_path) {
                manifests.insert(manifest_path);
            }
        }
    }

    manifests.into_iter().collect()
}

fn expand_workspace_member_pattern(workspace_dir: &Path, pattern: &str) -> Vec<PathBuf> {
    if !contains_wildcard(pattern) {
        return vec![workspace_dir.join(pattern)];
    }

    let normalized = pattern.replace('\\', "/");
    let components: Vec<&str> =
        normalized.split('/').filter(|component| !component.is_empty()).collect();
    let mut matches = Vec::new();
    expand_workspace_pattern_components(workspace_dir, &components, &mut matches);
    matches
}

fn expand_workspace_pattern_components(
    base: &Path,
    components: &[&str],
    matches: &mut Vec<PathBuf>,
) {
    if components.is_empty() {
        matches.push(base.to_path_buf());
        return;
    }

    let component = components[0];
    if component == "." {
        expand_workspace_pattern_components(base, &components[1..], matches);
        return;
    }

    if component == "**" {
        expand_workspace_pattern_components(base, &components[1..], matches);
        let entries = match std::fs::read_dir(base) {
            Ok(entries) => entries,
            Err(_) => return,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if is_non_symlink_dir(&path) {
                expand_workspace_pattern_components(&path, components, matches);
            }
        }
        return;
    }

    if contains_wildcard(component) {
        let entries = match std::fs::read_dir(base) {
            Ok(entries) => entries,
            Err(_) => return,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if !is_non_symlink_dir(&path) {
                continue;
            }
            let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
                continue;
            };
            if wildcard_matches(component, name) {
                expand_workspace_pattern_components(&path, &components[1..], matches);
            }
        }
        return;
    }

    let next = base.join(component);
    if is_non_symlink_dir(&next) {
        expand_workspace_pattern_components(&next, &components[1..], matches);
    }
}

fn is_non_symlink_dir(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok_and(|metadata| metadata.file_type().is_dir())
}

fn is_non_symlink_file(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok_and(|metadata| metadata.file_type().is_file())
}

fn contains_wildcard(pattern: &str) -> bool {
    pattern.contains('*') || pattern.contains('?')
}

fn wildcard_matches(pattern: &str, value: &str) -> bool {
    let pattern: Vec<char> = pattern.chars().collect();
    let value: Vec<char> = value.chars().collect();
    let mut dp = vec![vec![false; value.len() + 1]; pattern.len() + 1];
    dp[0][0] = true;

    for i in 0..pattern.len() {
        match pattern[i] {
            '*' => {
                dp[i + 1][0] = dp[i][0];
                for j in 0..value.len() {
                    dp[i + 1][j + 1] = dp[i][j + 1] || dp[i + 1][j];
                }
            }
            '?' => {
                for j in 0..value.len() {
                    dp[i + 1][j + 1] = dp[i][j];
                }
            }
            ch => {
                for j in 0..value.len() {
                    dp[i + 1][j + 1] = dp[i][j] && ch == value[j];
                }
            }
        }
    }

    dp[pattern.len()][value.len()]
}

fn canonicalize_or_self(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

// ---------------------------------------------------------------------------
// Function extraction
// ---------------------------------------------------------------------------

/// Parse a Rust source file and extract function signatures.
///
/// This is a lightweight parser that finds `fn` declarations and associated
/// native `requires` / `ensures` signature clauses and compatibility
/// `#[requires]` / `#[ensures]` attributes. It does NOT build an AST, but it
/// first sanitizes comments and strings and collects multiline signatures so
/// obvious non-code text and wrapped headers do not drive extraction.
pub(crate) fn extract_functions(file: &Path) -> Vec<ParsedFunction> {
    let content = match read_bounded_utf8_file(file, MAX_SAVED_PROOF_REPORT_BYTES) {
        Ok(c) => c,
        Err(_) => return Vec::new(),
    };
    extract_functions_from_source(&content, file)
}

/// Extract functions from source text (testable without filesystem).
pub(crate) fn extract_functions_from_source(source: &str, file: &Path) -> Vec<ParsedFunction> {
    let mut functions = Vec::new();
    let mut pending_requires = false;
    let mut pending_ensures = false;
    let sanitized_lines = sanitize_rust_source_lines(source);
    let mut macro_delimiter_depth = 0isize;
    let mut line_idx = 0;

    while line_idx < sanitized_lines.len() {
        let trimmed = sanitized_lines[line_idx].tokens.trim();

        if trimmed.is_empty() {
            line_idx += 1;
            continue;
        }

        if macro_delimiter_depth > 0 {
            macro_delimiter_depth += delimiter_delta(trimmed);
            macro_delimiter_depth = macro_delimiter_depth.max(0);
            line_idx += 1;
            continue;
        }

        if let Some((kind, end_idx)) = collect_attribute(&sanitized_lines, line_idx) {
            match kind {
                Some(ContractAttrKind::Requires) => pending_requires = true,
                Some(ContractAttrKind::Ensures) => pending_ensures = true,
                None => {}
            }
            line_idx = end_idx + 1;
            continue;
        }

        if is_macro_invocation_or_definition(trimmed) {
            pending_requires = false;
            pending_ensures = false;
            macro_delimiter_depth = delimiter_delta(trimmed).max(0);
            line_idx += 1;
            continue;
        }

        if let Some((func, end_idx)) = try_collect_fn_header(&sanitized_lines, line_idx, file) {
            let mut func = func;
            func.has_requires |= pending_requires;
            func.has_ensures |= pending_ensures;
            functions.push(func);
            pending_requires = false;
            pending_ensures = false;
            line_idx = end_idx + 1;
            continue;
        }

        pending_requires = false;
        pending_ensures = false;
        line_idx += 1;
    }

    functions
}

fn collect_attribute(
    lines: &[SanitizedLine],
    start_idx: usize,
) -> Option<(Option<ContractAttrKind>, usize)> {
    let first = lines.get(start_idx)?.tokens.trim();
    if !first.starts_with("#[") {
        return None;
    }

    let kind = contract_attr_kind(first);
    let mut bracket_depth = 0isize;
    for (line_idx, line) in lines.iter().enumerate().skip(start_idx) {
        bracket_depth += square_bracket_delta(line.tokens.as_str());
        if bracket_depth <= 0 {
            return Some((kind, line_idx));
        }
    }

    Some((kind, lines.len().saturating_sub(1)))
}

fn try_collect_fn_header(
    lines: &[SanitizedLine],
    start_idx: usize,
    file: &Path,
) -> Option<(ParsedFunction, usize)> {
    let first = lines.get(start_idx)?.tokens.trim();
    if !could_start_function_header(first) {
        return None;
    }

    let mut header = String::new();
    let mut saw_fn = false;
    let mut paren_depth = 0isize;
    let max_header_lines = (start_idx + 64).min(lines.len());

    for (line_idx, line) in lines.iter().enumerate().take(max_header_lines).skip(start_idx) {
        let trimmed = line.tokens.trim();
        if trimmed.is_empty() {
            continue;
        }
        if !header.is_empty() {
            header.push(' ');
        }
        header.push_str(trimmed);
        saw_fn |= contains_fn_keyword(trimmed);
        paren_depth += paren_delta(trimmed);

        if saw_fn && paren_depth <= 0 && (trimmed.contains('{') || trimmed.contains(';')) {
            return try_parse_fn_line(&header, file, start_idx + 1).map(|mut func| {
                let (has_requires, has_ensures) = native_signature_clause_presence(&header);
                func.has_requires = has_requires;
                func.has_ensures = has_ensures;
                (func, line_idx)
            });
        }

        if !saw_fn && line_idx > start_idx && !could_continue_function_prefix(trimmed) {
            return None;
        }
    }

    None
}

fn could_start_function_header(line: &str) -> bool {
    line.starts_with("fn ")
        || line.starts_with("pub")
        || line.starts_with("unsafe ")
        || line.starts_with("async ")
        || line.starts_with("const ")
        || line.starts_with("extern ")
}

fn could_continue_function_prefix(line: &str) -> bool {
    line.starts_with("fn ")
        || line.starts_with("unsafe ")
        || line.starts_with("async ")
        || line.starts_with("const ")
        || line.starts_with("extern ")
}

fn contains_fn_keyword(line: &str) -> bool {
    let mut search_start = 0;
    while let Some(relative_idx) = line[search_start..].find("fn") {
        let idx = search_start + relative_idx;
        let before = line[..idx].chars().next_back();
        let after = line[idx + "fn".len()..].chars().next();
        if before.is_none_or(|ch| !is_rust_ident_continue(ch))
            && after.is_none_or(|ch| !is_rust_ident_continue(ch))
        {
            return true;
        }
        search_start = idx + 1;
    }
    false
}

fn is_macro_invocation_or_definition(line: &str) -> bool {
    if line.starts_with("macro_rules!") {
        return true;
    }

    let Some(bang_idx) = line.find('!') else {
        return false;
    };
    let before_bang = line[..bang_idx].trim_end();
    let name_start = before_bang
        .char_indices()
        .rev()
        .find(|(_, ch)| !is_rust_ident_continue(*ch))
        .map_or(0, |(idx, ch)| idx + ch.len_utf8());
    let macro_name = before_bang[name_start..].trim();
    !macro_name.is_empty()
        && macro_name.chars().all(is_rust_ident_continue)
        && line[bang_idx + 1..].trim_start().starts_with(['(', '[', '{'])
}

fn delimiter_delta(line: &str) -> isize {
    line.chars()
        .map(|ch| match ch {
            '(' | '[' | '{' => 1,
            ')' | ']' | '}' => -1,
            _ => 0,
        })
        .sum()
}

fn square_bracket_delta(line: &str) -> isize {
    line.chars()
        .map(|ch| match ch {
            '[' => 1,
            ']' => -1,
            _ => 0,
        })
        .sum()
}

fn paren_delta(line: &str) -> isize {
    line.chars()
        .map(|ch| match ch {
            '(' => 1,
            ')' => -1,
            _ => 0,
        })
        .sum()
}

#[derive(Clone, Copy)]
enum ContractAttrKind {
    Requires,
    Ensures,
}

fn contract_attr_kind(line: &str) -> Option<ContractAttrKind> {
    let inner = line.strip_prefix("#[")?.trim_start();
    let name_end = inner.find(['(', '=', ' ', ']']).unwrap_or(inner.len());
    let name = inner[..name_end].trim();
    let name = name.rsplit("::").next().unwrap_or(name);

    match name {
        "requires" | "contracts_requires" | "trust_requires" => Some(ContractAttrKind::Requires),
        "ensures" | "contracts_ensures" | "trust_ensures" => Some(ContractAttrKind::Ensures),
        _ => None,
    }
}

/// Try to parse a line as a function declaration.
fn try_parse_fn_line(line: &str, file: &Path, line_num: usize) -> Option<ParsedFunction> {
    // Patterns we recognize:
    //   fn name(...)
    //   pub fn name(...)
    //   pub(crate) fn name(...)
    //   pub(super) fn name(...)
    //   unsafe fn name(...)
    //   pub unsafe fn name(...)
    //   async fn name(...)
    //   pub async fn name(...)
    //   pub async unsafe fn name(...)
    //   const fn name(...)

    let mut rest = line;
    let mut is_public = false;
    let mut is_unsafe = false;

    // Strip visibility
    if rest.starts_with("pub") {
        is_public = true;
        rest = rest[3..].trim_start();
        // pub(crate), pub(super), etc.
        if rest.starts_with('(') {
            if let Some(close) = rest.find(')') {
                rest = rest[close + 1..].trim_start();
            }
        }
    }

    // Strip qualifiers: const, async, unsafe, extern
    loop {
        if let Some(after) = rest.strip_prefix("const ") {
            rest = after.trim_start();
        } else if let Some(after) = rest.strip_prefix("async ") {
            rest = after.trim_start();
        } else if let Some(after) = rest.strip_prefix("unsafe ") {
            is_unsafe = true;
            rest = after.trim_start();
        } else if let Some(after) = rest.strip_prefix("extern ") {
            rest = after.trim_start();
            // Skip optional ABI string: extern "C"
            if rest.starts_with('"') {
                if let Some(close) = rest[1..].find('"') {
                    rest = rest[close + 2..].trim_start();
                }
            }
        } else {
            break;
        }
    }

    // Must start with "fn "
    rest = rest.strip_prefix("fn ")?;
    rest = rest.trim_start();

    // Extract function name (up to `(` or `<`)
    let name_end = rest.find(|c: char| c == '(' || c == '<' || c.is_whitespace())?;
    let name = rest[..name_end].to_string();

    // Basic validation: name should be a valid identifier
    if name.is_empty() || !name.chars().next()?.is_alphanumeric() && name.chars().next()? != '_' {
        return None;
    }

    // Extract parameters (rough: everything between first ( and matching ))
    let params = extract_param_names(rest);
    let typed_params = extract_typed_params(rest);

    // Extract return type
    let return_type = extract_return_type(rest);

    Some(ParsedFunction {
        name,
        file: file.to_path_buf(),
        line: line_num,
        is_public,
        is_unsafe,
        has_requires: false,
        has_ensures: false,
        return_type,
        params,
        typed_params,
    })
}

fn split_top_level_commas(input: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut start = 0;
    let mut paren_depth = 0isize;
    let mut bracket_depth = 0isize;
    let mut brace_depth = 0isize;
    let mut angle_depth = 0isize;

    for (idx, ch) in input.char_indices() {
        match ch {
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            '[' => bracket_depth += 1,
            ']' => bracket_depth -= 1,
            '{' => brace_depth += 1,
            '}' => brace_depth -= 1,
            '<' => angle_depth += 1,
            '>' => angle_depth = (angle_depth - 1).max(0),
            ',' if paren_depth == 0
                && bracket_depth == 0
                && brace_depth == 0
                && angle_depth == 0 =>
            {
                parts.push(input[start..idx].trim());
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }

    parts.push(input[start..].trim());
    parts
}

fn parameter_list_bounds(sig: &str) -> Option<(usize, usize)> {
    let paren_start = sig.find('(')?;
    let mut depth = 0isize;
    for (relative_idx, ch) in sig[paren_start..].char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some((paren_start + 1, paren_start + relative_idx));
                }
            }
            _ => {}
        }
    }

    None
}

fn normalize_param_name(name: &str) -> String {
    name.trim().strip_prefix("mut ").unwrap_or(name.trim()).trim().to_string()
}

fn top_level_return_arrow(after_params: &str) -> Option<usize> {
    let mut paren_depth = 0isize;
    let mut bracket_depth = 0isize;
    let mut brace_depth = 0isize;
    let chars: Vec<char> = after_params.chars().collect();
    let mut idx = 0;
    while idx < chars.len() {
        match chars[idx] {
            '(' => paren_depth += 1,
            ')' => paren_depth -= 1,
            '[' => bracket_depth += 1,
            ']' => bracket_depth -= 1,
            '{' => brace_depth += 1,
            '}' => brace_depth -= 1,
            '-' if chars.get(idx + 1) == Some(&'>')
                && paren_depth == 0
                && bracket_depth == 0
                && brace_depth == 0 =>
            {
                return Some(idx);
            }
            _ => {}
        }
        idx += 1;
    }

    None
}

/// Extract parameter names from a function signature line.
fn extract_param_names(sig: &str) -> Vec<String> {
    let Some((params_start, params_end)) = parameter_list_bounds(sig) else {
        return Vec::new();
    };
    let params_str = &sig[params_start..params_end];
    if params_str.trim().is_empty() {
        return Vec::new();
    }

    split_top_level_commas(params_str)
        .into_iter()
        .filter_map(|p| {
            let p = p.trim();
            if p == "self" || p == "&self" || p == "&mut self" || p == "mut self" {
                Some("self".to_string())
            } else {
                // "name: Type" -> extract name
                p.split(':').next().map(normalize_param_name)
            }
        })
        .filter(|n| !n.is_empty())
        .collect()
}

/// Extract parameters with their types from a function signature line.
///
/// Returns `(name, type)` pairs. Self parameters are skipped since they
/// don't carry useful type information for spec inference.
fn extract_typed_params(sig: &str) -> Vec<(String, String)> {
    let Some((params_start, params_end)) = parameter_list_bounds(sig) else {
        return Vec::new();
    };
    let params_str = &sig[params_start..params_end];
    if params_str.trim().is_empty() {
        return Vec::new();
    }

    split_top_level_commas(params_str)
        .into_iter()
        .filter_map(|p| {
            let p = p.trim();
            // Skip self parameters
            if p == "self" || p == "&self" || p == "&mut self" || p == "mut self" {
                return None;
            }
            // "name: Type" -> (name, Type)
            let colon_pos = p.find(':')?;
            let name = normalize_param_name(&p[..colon_pos]);
            let ty = p[colon_pos + 1..].trim().to_string();
            if name.is_empty() || ty.is_empty() {
                return None;
            }
            Some((name, ty))
        })
        .collect()
}

/// Extract the return type from a function signature line.
fn extract_return_type(sig: &str) -> Option<String> {
    let (_, params_end) = parameter_list_bounds(sig)?;
    let after_params = &sig[params_end + 1..];
    let arrow_pos = top_level_return_arrow(after_params)?;
    let after_arrow = after_params[arrow_pos + 2..].trim();
    // Return type ends at `{`, `where`, a native contract clause, or end of line.
    let end = after_arrow.find(['{', '\n']).unwrap_or(after_arrow.len());
    let ret = after_arrow[..end].trim();
    let ret = ret.find(" where ").map_or(ret, |where_idx| ret[..where_idx].trim());
    let ret = contract_clause_start(ret).map_or(ret, |clause_idx| ret[..clause_idx].trim());
    if ret.is_empty() { None } else { Some(ret.to_string()) }
}

fn native_signature_clause_presence(sig: &str) -> (bool, bool) {
    let Some((_, params_end)) = parameter_list_bounds(sig) else {
        return (false, false);
    };
    let suffix = &sig[params_end + 1..];
    let suffix = suffix.split('{').next().unwrap_or(suffix);
    (
        contains_contract_clause_keyword(suffix, "requires"),
        contains_contract_clause_keyword(suffix, "ensures"),
    )
}

fn contract_clause_start(text: &str) -> Option<usize> {
    ["requires", "ensures"]
        .into_iter()
        .filter_map(|keyword| contract_clause_keyword_position(text, keyword))
        .min()
}

fn contains_contract_clause_keyword(text: &str, keyword: &str) -> bool {
    contract_clause_keyword_position(text, keyword).is_some()
}

fn contract_clause_keyword_position(text: &str, keyword: &str) -> Option<usize> {
    text.match_indices(keyword).find_map(|(index, _)| {
        let before = text[..index].chars().next_back();
        let after = text[index + keyword.len()..].chars().next();
        let starts_token = before.is_none_or(|ch| !is_rust_ident_continue(ch));
        let ends_token = after.is_none_or(|ch| !is_rust_ident_continue(ch));
        (starts_token && ends_token).then_some(index)
    })
}

// ---------------------------------------------------------------------------
// VC generation
// ---------------------------------------------------------------------------

/// Generate standalone VCs from a list of parsed functions.
pub(crate) fn generate_standalone_vcs(functions: &[ParsedFunction]) -> Vec<StandaloneVc> {
    generate_standalone_vcs_with_options(functions, SourceAnalysisOptions::default())
}

/// Generate standalone VCs from a list of parsed functions and profile options.
pub(crate) fn generate_standalone_vcs_with_options(
    functions: &[ParsedFunction],
    options: SourceAnalysisOptions,
) -> Vec<StandaloneVc> {
    let mut vcs = Vec::new();

    for func in functions {
        // VC: requires spec present
        if func.has_requires {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::PreconditionPresent,
                description: format!("{}: requires specification present", func.name),
                outcome: StandaloneOutcome::Present,
            });
        }

        // VC: ensures spec present
        if func.has_ensures {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::PostconditionPresent,
                description: format!("{}: ensures specification present", func.name),
                outcome: StandaloneOutcome::Present,
            });
        }

        // VC: unsafe function needs audit
        if func.is_unsafe {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::UnsafeFunction,
                description: format!("{}: unsafe function requires safety proof", func.name),
                outcome: StandaloneOutcome::Unknown,
            });
        }

        // VC: public function without specs
        if func.is_public && !func.has_requires && !func.has_ensures {
            vcs.push(StandaloneVc {
                function: func.name.clone(),
                file: func.file.clone(),
                kind: VcKind::UnspecifiedPublicApi,
                description: format!("{}: public function has no specification", func.name),
                outcome: StandaloneOutcome::Unknown,
            });
        }
    }

    if options.hardened {
        vcs.extend(generate_hardened_source_vcs(functions));
    }

    vcs
}

struct HardenedRule {
    token: &'static str,
    kind: VcKind,
    description: &'static str,
    require_call_context: bool,
}

const HARDENED_RULES: &[HardenedRule] = &[
    HardenedRule {
        token: "std::fs::remove_file(",
        kind: VcKind::HardenedRawPathApi,
        description: "raw path removal re-resolves a mutable directory entry; use a verified dirfd/handle-relative wrapper",
        require_call_context: true,
    },
    HardenedRule {
        token: "fs::remove_file(",
        kind: VcKind::HardenedRawPathApi,
        description: "raw path removal re-resolves a mutable directory entry; use a verified dirfd/handle-relative wrapper",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::fs::remove_dir(",
        kind: VcKind::HardenedRawPathApi,
        description: "raw path directory removal re-resolves a mutable directory entry; use a verified dirfd/handle-relative wrapper",
        require_call_context: true,
    },
    HardenedRule {
        token: "fs::remove_dir(",
        kind: VcKind::HardenedRawPathApi,
        description: "raw path directory removal re-resolves a mutable directory entry; use a verified dirfd/handle-relative wrapper",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::fs::rename(",
        kind: VcKind::HardenedRawPathApi,
        description: "raw rename is name-based and needs a direntry identity contract in hardened code",
        require_call_context: true,
    },
    HardenedRule {
        token: "fs::rename(",
        kind: VcKind::HardenedRawPathApi,
        description: "raw rename is name-based and needs a direntry identity contract in hardened code",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::fs::canonicalize(",
        kind: VcKind::HardenedPathIdentity,
        description: "canonicalization is not a filesystem identity proof; compare stable file identity instead",
        require_call_context: true,
    },
    HardenedRule {
        token: "fs::canonicalize(",
        kind: VcKind::HardenedPathIdentity,
        description: "canonicalization is not a filesystem identity proof; compare stable file identity instead",
        require_call_context: true,
    },
    HardenedRule {
        token: "Path::new(\"/\")",
        kind: VcKind::HardenedPathIdentity,
        description: "root/path spelling comparison is not stable filesystem identity; compare resolved file identity under the OS model",
        require_call_context: false,
    },
    HardenedRule {
        token: "std::fs::metadata(",
        kind: VcKind::HardenedRawPathApi,
        description: "metadata on a path is a path-resolution check; a later path operation needs a stable handle proof",
        require_call_context: true,
    },
    HardenedRule {
        token: "fs::metadata(",
        kind: VcKind::HardenedRawPathApi,
        description: "metadata on a path is a path-resolution check; a later path operation needs a stable handle proof",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::fs::set_permissions(",
        kind: VcKind::HardenedPermissionChange,
        description: "path-based permission changes need a stable identity and creation-time mode proof",
        require_call_context: true,
    },
    HardenedRule {
        token: "fs::set_permissions(",
        kind: VcKind::HardenedPermissionChange,
        description: "path-based permission changes need a stable identity and creation-time mode proof",
        require_call_context: true,
    },
    HardenedRule {
        token: "File::create(",
        kind: VcKind::HardenedRawPathApi,
        description: "File::create uses path resolution and default creation semantics; use create-at with explicit mode/identity contracts",
        require_call_context: true,
    },
    HardenedRule {
        token: "File::open(",
        kind: VcKind::HardenedRawPathApi,
        description: "File::open uses path resolution; use a verified dirfd/handle-relative wrapper in hardened code",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::fs::File::open(",
        kind: VcKind::HardenedRawPathApi,
        description: "File::open uses path resolution; use a verified dirfd/handle-relative wrapper in hardened code",
        require_call_context: true,
    },
    HardenedRule {
        token: ".open(",
        kind: VcKind::HardenedRawPathApi,
        description: "OpenOptions::open on a path needs explicit no-follow/create/mode and trust-domain contracts",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::fs::create_dir(",
        kind: VcKind::HardenedPermissionCreate,
        description: "directory creation by path needs creation-time permissions and parent dirfd contracts",
        require_call_context: true,
    },
    HardenedRule {
        token: "fs::create_dir(",
        kind: VcKind::HardenedPermissionCreate,
        description: "directory creation by path needs creation-time permissions and parent dirfd contracts",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::fs::create_dir_all(",
        kind: VcKind::HardenedPermissionCreate,
        description: "recursive directory creation by path needs explicit mode, umask, and parent dirfd contracts",
        require_call_context: true,
    },
    HardenedRule {
        token: "fs::create_dir_all(",
        kind: VcKind::HardenedPermissionCreate,
        description: "recursive directory creation by path needs explicit mode, umask, and parent dirfd contracts",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::fs::read_to_string(",
        kind: VcKind::HardenedUtf8Boundary,
        description: "read_to_string rejects non-UTF-8 data; Unix boundary data must stay byte-exact unless UTF-8 is proven",
        require_call_context: true,
    },
    HardenedRule {
        token: "fs::read_to_string(",
        kind: VcKind::HardenedUtf8Boundary,
        description: "read_to_string rejects non-UTF-8 data; Unix boundary data must stay byte-exact unless UTF-8 is proven",
        require_call_context: true,
    },
    HardenedRule {
        token: ".read_to_string(",
        kind: VcKind::HardenedUtf8Boundary,
        description: "Read::read_to_string rejects non-UTF-8 data; Unix boundary data must stay byte-exact unless UTF-8 is proven",
        require_call_context: true,
    },
    HardenedRule {
        token: "from_utf8_lossy",
        kind: VcKind::HardenedByteLoss,
        description: "lossy UTF-8 conversion can corrupt byte-exact input/output",
        require_call_context: true,
    },
    HardenedRule {
        token: "to_string_lossy",
        kind: VcKind::HardenedByteLoss,
        description: "lossy OS/path conversion can corrupt byte-exact filesystem data",
        require_call_context: true,
    },
    HardenedRule {
        token: "String::from_utf8(",
        kind: VcKind::HardenedUtf8Boundary,
        description: "strict UTF-8 conversion can reject valid Unix filenames or byte streams",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::str::from_utf8(",
        kind: VcKind::HardenedUtf8Boundary,
        description: "strict UTF-8 conversion can reject valid Unix filenames or byte streams",
        require_call_context: true,
    },
    HardenedRule {
        token: ".to_str().unwrap",
        kind: VcKind::HardenedUtf8Boundary,
        description: "unchecked OS/path UTF-8 conversion rejects valid non-UTF-8 boundary data",
        require_call_context: true,
    },
    HardenedRule {
        token: ".ok()",
        kind: VcKind::HardenedErrorDiscard,
        description: "Result::ok discards the error channel; hardened code needs a proof-bearing allow or propagation",
        require_call_context: true,
    },
    HardenedRule {
        token: ".unwrap_or_default()",
        kind: VcKind::HardenedErrorDiscard,
        description: "unwrap_or_default can erase an error into a successful default value",
        require_call_context: true,
    },
    HardenedRule {
        token: "let _ =",
        kind: VcKind::HardenedErrorDiscard,
        description: "discarded value may be a Result or status; hardened code requires an explicit checked discard reason",
        require_call_context: true,
    },
    HardenedRule {
        token: ".unwrap()",
        kind: VcKind::HardenedPanic,
        description: "unwrap is a denial-of-service path unless the success precondition is proven",
        require_call_context: true,
    },
    HardenedRule {
        token: ".expect(",
        kind: VcKind::HardenedPanic,
        description: "expect is a denial-of-service path unless the success precondition is proven",
        require_call_context: true,
    },
    HardenedRule {
        token: "panic!(",
        kind: VcKind::HardenedPanic,
        description: "explicit panic escapes the hardened no-DoS profile",
        require_call_context: true,
    },
    HardenedRule {
        token: "todo!(",
        kind: VcKind::HardenedPanic,
        description: "todo! panics at runtime and cannot pass a hardened boundary",
        require_call_context: true,
    },
    HardenedRule {
        token: "unreachable!(",
        kind: VcKind::HardenedPanic,
        description: "unreachable! must be justified by a proof, not a runtime panic path",
        require_call_context: true,
    },
    HardenedRule {
        token: "assert!(",
        kind: VcKind::HardenedPanic,
        description: "assert! is a panic boundary; hardened public code needs a proved precondition or checked error",
        require_call_context: true,
    },
    HardenedRule {
        token: "chroot(",
        kind: VcKind::HardenedTrustBoundary,
        description: "root changes must be ordered with name-service, dynamic loading, and privilege-drop effects",
        require_call_context: true,
    },
    HardenedRule {
        token: "setuid(",
        kind: VcKind::HardenedTrustBoundary,
        description: "privilege transition requires a modeled privilege-state contract",
        require_call_context: true,
    },
    HardenedRule {
        token: "setgid(",
        kind: VcKind::HardenedTrustBoundary,
        description: "privilege transition requires a modeled privilege-state contract",
        require_call_context: true,
    },
    HardenedRule {
        token: "get_user_by_name",
        kind: VcKind::HardenedTrustBoundary,
        description: "name-service lookup may read attacker-controlled NSS/passwd data after a root/domain change",
        require_call_context: true,
    },
    HardenedRule {
        token: "getpwnam",
        kind: VcKind::HardenedTrustBoundary,
        description: "libc name-service lookup may load configuration or modules from the active trust domain",
        require_call_context: true,
    },
    HardenedRule {
        token: "dlopen",
        kind: VcKind::HardenedTrustBoundary,
        description: "dynamic loading must be proven to occur in a trusted domain while privileged",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::env::args()",
        kind: VcKind::HardenedCompatibility,
        description: "CLI boundary uses Unicode String args; compatibility-sensitive tools should model OsString/byte arguments",
        require_call_context: true,
    },
    HardenedRule {
        token: "env::args()",
        kind: VcKind::HardenedCompatibility,
        description: "CLI boundary uses Unicode String args; compatibility-sensitive tools should model OsString/byte arguments",
        require_call_context: true,
    },
    HardenedRule {
        token: "std::io::stdout()",
        kind: VcKind::HardenedProcessSemantics,
        description: "stdout pipe behavior depends on SIGPIPE/startup semantics; compatibility-sensitive tools need an explicit process-signal policy",
        require_call_context: true,
    },
    HardenedRule {
        token: "io::stdout()",
        kind: VcKind::HardenedProcessSemantics,
        description: "stdout pipe behavior depends on SIGPIPE/startup semantics; compatibility-sensitive tools need an explicit process-signal policy",
        require_call_context: true,
    },
    HardenedRule {
        token: "print!(",
        kind: VcKind::HardenedProcessSemantics,
        description: "stdout writes must model broken-pipe/SIGPIPE compatibility instead of assuming Rust default process semantics",
        require_call_context: true,
    },
    HardenedRule {
        token: "println!(",
        kind: VcKind::HardenedProcessSemantics,
        description: "stdout writes must model broken-pipe/SIGPIPE compatibility instead of assuming Rust default process semantics",
        require_call_context: true,
    },
    HardenedRule {
        token: "extern \"",
        kind: VcKind::HardenedFfiBoundary,
        description: "extern boundary is inventory until ABI, memory, and trust evidence are attached",
        require_call_context: false,
    },
    HardenedRule {
        token: "unsafe {",
        kind: VcKind::HardenedUnsafeOperation,
        description: "unsafe block needs a trusted-wrapper contract and evidence before hardened code can rely on it",
        require_call_context: true,
    },
];

fn generate_hardened_source_vcs(functions: &[ParsedFunction]) -> Vec<StandaloneVc> {
    let mut by_file: BTreeMap<PathBuf, Vec<&ParsedFunction>> = BTreeMap::new();
    for func in functions {
        by_file.entry(func.file.clone()).or_default().push(func);
    }

    let mut vcs = Vec::new();
    for (file, funcs) in by_file {
        let Ok(source) = read_bounded_utf8_file(&file, MAX_SAVED_PROOF_REPORT_BYTES) else {
            continue;
        };
        vcs.extend(generate_hardened_source_vcs_from_source(&source, &file, &funcs));
    }
    vcs
}

fn generate_hardened_source_vcs_from_source(
    source: &str,
    file: &Path,
    functions: &[&ParsedFunction],
) -> Vec<StandaloneVc> {
    let mut vcs = Vec::new();
    let mut create_seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut trust_transition_seen: BTreeMap<String, (usize, &'static str)> = BTreeMap::new();
    let function_starts: BTreeMap<usize, (String, String)> = functions
        .iter()
        .map(|func| (func.line, (func.name.clone(), format!("{}:{}", func.name, func.line))))
        .collect();
    let module_function = module_function_name(file);
    let module_context = (module_function.clone(), format!("{module_function}:0"));
    let mut active_function: Option<(String, String)> = None;
    let mut brace_depth: isize = 0;
    let mut pending_split_unsafe: BTreeMap<String, (String, usize)> = BTreeMap::new();
    let sanitized_lines = sanitize_rust_source_lines(source);

    for (line_idx, sanitized) in sanitized_lines.iter().enumerate() {
        let line_no = line_idx + 1;
        let code = sanitized.code.as_str();
        let tokens = sanitized.tokens.as_str();
        let trimmed_code = code.trim();
        let trimmed_tokens = tokens.trim();
        if trimmed_code.is_empty() && trimmed_tokens.is_empty() {
            continue;
        }

        if let Some(function) = function_starts.get(&line_no) {
            active_function = Some(function.clone());
            brace_depth = 0;
        }

        if let Some((function, function_key)) = active_function.clone() {
            let segment = active_function_line_segment(code, tokens, brace_depth);
            scan_hardened_segment(
                &mut vcs,
                file,
                line_no,
                segment.active_code,
                segment.active_tokens,
                &function,
                &function_key,
                &mut create_seen,
                &mut trust_transition_seen,
                &mut pending_split_unsafe,
            );

            let active_trimmed_code = segment.active_code.trim();
            let active_trimmed_tokens = segment.active_tokens.trim();
            let is_declaration = is_function_declaration_line(active_trimmed_code, file, line_no);
            if segment.closed
                || (is_declaration
                    && active_trimmed_tokens.ends_with(';')
                    && !active_trimmed_tokens.contains('{'))
            {
                active_function = None;
                brace_depth = 0;
                scan_hardened_segment(
                    &mut vcs,
                    file,
                    line_no,
                    segment.suffix_code,
                    segment.suffix_tokens,
                    &module_context.0,
                    &module_context.1,
                    &mut create_seen,
                    &mut trust_transition_seen,
                    &mut pending_split_unsafe,
                );
            } else {
                brace_depth = segment.brace_depth;
            }
        } else {
            scan_hardened_segment(
                &mut vcs,
                file,
                line_no,
                code,
                tokens,
                &module_context.0,
                &module_context.1,
                &mut create_seen,
                &mut trust_transition_seen,
                &mut pending_split_unsafe,
            );
        }
    }

    vcs
}

struct ActiveFunctionLineSegment<'a> {
    active_code: &'a str,
    active_tokens: &'a str,
    suffix_code: &'a str,
    suffix_tokens: &'a str,
    brace_depth: isize,
    closed: bool,
}

fn active_function_line_segment<'a>(
    code: &'a str,
    tokens: &'a str,
    starting_depth: isize,
) -> ActiveFunctionLineSegment<'a> {
    let mut depth = starting_depth;
    let mut saw_open = starting_depth > 0;
    let mut active_code_start = 0;
    let mut active_token_start = 0;

    for (idx, ch) in tokens.char_indices() {
        match ch {
            '{' => {
                depth += 1;
                if !saw_open && starting_depth == 0 {
                    let token_split = idx + ch.len_utf8();
                    let chars_in_prefix = tokens[..token_split].chars().count();
                    active_code_start = byte_index_after_chars(code, chars_in_prefix);
                    active_token_start = token_split;
                }
                saw_open = true;
            }
            '}' => {
                depth -= 1;
                if saw_open && depth <= 0 {
                    let token_split = idx + ch.len_utf8();
                    let chars_in_prefix = tokens[..token_split].chars().count();
                    let code_split = byte_index_after_chars(code, chars_in_prefix);
                    return ActiveFunctionLineSegment {
                        active_code: &code[active_code_start..code_split],
                        active_tokens: &tokens[active_token_start..token_split],
                        suffix_code: &code[code_split..],
                        suffix_tokens: &tokens[token_split..],
                        brace_depth: 0,
                        closed: true,
                    };
                }
            }
            _ => {}
        }
    }

    ActiveFunctionLineSegment {
        active_code: &code[active_code_start..],
        active_tokens: &tokens[active_token_start..],
        suffix_code: "",
        suffix_tokens: "",
        brace_depth: depth,
        closed: false,
    }
}

fn byte_index_after_chars(text: &str, char_count: usize) -> usize {
    text.char_indices().nth(char_count).map_or(text.len(), |(idx, _)| idx)
}

fn scan_hardened_segment(
    vcs: &mut Vec<StandaloneVc>,
    file: &Path,
    line_no: usize,
    code: &str,
    tokens: &str,
    function: &str,
    function_key: &str,
    create_seen: &mut BTreeMap<String, usize>,
    trust_transition_seen: &mut BTreeMap<String, (usize, &'static str)>,
    pending_split_unsafe: &mut BTreeMap<String, (String, usize)>,
) {
    let trimmed_code = code.trim();
    let trimmed_tokens = tokens.trim();
    if trimmed_code.is_empty() && trimmed_tokens.is_empty() {
        return;
    }

    if let Some((pending_function, pending_line)) = pending_split_unsafe.remove(function_key) {
        if trimmed_tokens.starts_with('{') {
            push_hardened_vc(
                vcs,
                file,
                pending_line,
                &pending_function,
                VcKind::HardenedUnsafeOperation,
                "unsafe block needs a trusted-wrapper contract and evidence before hardened code can rely on it",
            );
        }
    }

    let is_declaration =
        is_function_declaration_line(trimmed_code, file, line_no) && !trimmed_tokens.contains('{');

    for rule in HARDENED_RULES {
        if !line_matches_hardened_rule(rule, trimmed_code, trimmed_tokens) {
            continue;
        }
        if rule.require_call_context && (!is_probable_call_site(trimmed_code) || is_declaration) {
            continue;
        }
        push_hardened_vc(vcs, file, line_no, function, rule.kind, rule.description);
    }

    if contains_split_line_unsafe_start(trimmed_tokens)
        && is_probable_call_site(trimmed_code)
        && !is_declaration
    {
        pending_split_unsafe.insert(function_key.to_string(), (function.to_string(), line_no));
    }

    if contains_hardened_create_api_call(trimmed_tokens)
        && is_probable_call_site(trimmed_code)
        && !is_declaration
    {
        create_seen.entry(function_key.to_string()).or_insert(line_no);
    }

    if contains_any_token(trimmed_tokens, &["set_permissions(", "set_owner(", "chown("])
        && is_probable_call_site(trimmed_code)
        && !is_declaration
    {
        if let Some(create_line) = create_seen.get(function_key).copied() {
            push_hardened_vc(
                vcs,
                file,
                line_no,
                function,
                VcKind::HardenedPermissionWindow,
                &format!(
                    "creation at line {create_line} is followed by a permission/owner change; create with final mode/owner under the OS model"
                ),
            );
        }
    }

    if let Some(transition) = trust_domain_transition(trimmed_tokens) {
        if is_probable_call_site(trimmed_code) && !is_declaration {
            trust_transition_seen.entry(function_key.to_string()).or_insert((line_no, transition));
        }
    }

    if contains_any_token(
        trimmed_tokens,
        &["get_user_by_name", "get_group_by_name", "getpwnam", "getgrnam", "dlopen"],
    ) && is_probable_call_site(trimmed_code)
        && !is_declaration
    {
        if let Some((transition_line, transition)) =
            trust_transition_seen.get(function_key).copied()
        {
            push_hardened_vc(
                vcs,
                file,
                line_no,
                function,
                VcKind::HardenedTrustDomainOrder,
                &format!(
                    "name-service or dynamic-loading effect after {transition} at line {transition_line}; resolve trusted inputs before crossing root/trust domains"
                ),
            );
        }
    }
}

#[derive(Default)]
struct SanitizedLine {
    code: String,
    tokens: String,
}

fn sanitize_rust_source_lines(source: &str) -> Vec<SanitizedLine> {
    let mut lines = vec![SanitizedLine::default()];
    let chars: Vec<char> = source.chars().collect();
    let mut i = 0;
    let mut block_comment_depth = 0usize;
    let mut string_state: Option<StringState> = None;

    while i < chars.len() {
        let ch = chars[i];
        if ch == '\n' {
            lines.push(SanitizedLine::default());
            i += 1;
            continue;
        }

        let line = lines.last_mut().expect("at least one sanitized line");
        if block_comment_depth > 0 {
            if ch == '/' && chars.get(i + 1) == Some(&'*') {
                block_comment_depth += 1;
                line.push_spaces(2);
                i += 2;
            } else if ch == '*' && chars.get(i + 1) == Some(&'/') {
                block_comment_depth -= 1;
                line.push_spaces(2);
                i += 2;
            } else {
                line.push_space();
                i += 1;
            }
            continue;
        }

        if let Some(state) = string_state {
            match state {
                StringState::Normal => {
                    line.push_code_space(ch);
                    if ch == '\\' {
                        if let Some(next) = chars.get(i + 1).copied() {
                            line.push_code_space(next);
                            i += 2;
                        } else {
                            i += 1;
                        }
                        continue;
                    }
                    if ch == '"' {
                        string_state = None;
                    }
                    i += 1;
                }
                StringState::Raw { hashes } => {
                    line.push_code_space(ch);
                    if ch == '"' && raw_hashes_close(&chars, i + 1, hashes) {
                        for offset in 0..hashes {
                            line.push_code_space(chars[i + 1 + offset]);
                        }
                        i += hashes + 1;
                        string_state = None;
                    } else {
                        i += 1;
                    }
                }
            }
            continue;
        }

        if ch == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                let line = lines.last_mut().expect("at least one sanitized line");
                line.push_space();
                i += 1;
            }
            continue;
        }

        if ch == '/' && chars.get(i + 1) == Some(&'*') {
            block_comment_depth = 1;
            line.push_spaces(2);
            i += 2;
            continue;
        }

        if let Some((prefix_len, hashes)) = raw_string_start(&chars, i) {
            for offset in 0..prefix_len {
                line.push_code_space(chars[i + offset]);
            }
            string_state = Some(StringState::Raw { hashes });
            i += prefix_len;
            continue;
        }

        if ch == 'b' && chars.get(i + 1) == Some(&'"') {
            line.push_code_space(ch);
            line.push_code_space('"');
            string_state = Some(StringState::Normal);
            i += 2;
            continue;
        }

        if ch == '"' {
            line.push_code_space(ch);
            string_state = Some(StringState::Normal);
            i += 1;
            continue;
        }

        line.push_code_token(ch);
        i += 1;
    }

    lines
}

#[derive(Clone, Copy)]
enum StringState {
    Normal,
    Raw { hashes: usize },
}

impl SanitizedLine {
    fn push_code_token(&mut self, ch: char) {
        self.code.push(ch);
        self.tokens.push(ch);
    }

    fn push_code_space(&mut self, ch: char) {
        self.code.push(ch);
        self.tokens.push(' ');
    }

    fn push_space(&mut self) {
        self.code.push(' ');
        self.tokens.push(' ');
    }

    fn push_spaces(&mut self, count: usize) {
        for _ in 0..count {
            self.push_space();
        }
    }
}

fn raw_string_start(chars: &[char], start: usize) -> Option<(usize, usize)> {
    let mut pos = start;
    if chars.get(pos) == Some(&'b') {
        if chars.get(pos + 1) != Some(&'r') {
            return None;
        }
        pos += 1;
    }
    if chars.get(pos) != Some(&'r') {
        return None;
    }
    pos += 1;
    let mut hashes = 0;
    while chars.get(pos) == Some(&'#') {
        hashes += 1;
        pos += 1;
    }
    if chars.get(pos) != Some(&'"') {
        return None;
    }
    Some((pos - start + 1, hashes))
}

fn raw_hashes_close(chars: &[char], start: usize, hashes: usize) -> bool {
    (0..hashes).all(|offset| chars.get(start + offset) == Some(&'#'))
}

fn line_matches_hardened_rule(rule: &HardenedRule, code: &str, tokens: &str) -> bool {
    match rule.token {
        "Path::new(\"/\")" => contains_root_path_identity_comparison(code, tokens),
        "extern \"" => is_extern_abi_boundary(code),
        token => contains_rule_token(tokens, token),
    }
}

fn contains_root_path_identity_comparison(code: &str, tokens: &str) -> bool {
    contains_path_new_root(code)
        && contains_any(&normalize_hardened_call_spacing(tokens), &["==", "!=", "matches!"])
}

fn contains_path_new_root(code: &str) -> bool {
    let normalized = normalize_hardened_call_spacing(code);
    let mut search_start = 0;
    while let Some(relative_idx) = normalized[search_start..].find("Path::new(") {
        let idx = search_start + relative_idx;
        if rust_call_left_boundary(&normalized, idx) {
            let args = &normalized[idx + "Path::new(".len()..];
            if args.starts_with("\"/\"") || args.starts_with("r\"/\"") {
                return true;
            }
        }
        search_start = idx + 1;
    }
    false
}

fn is_extern_abi_boundary(code: &str) -> bool {
    let trimmed = code.trim_start();
    if trimmed.starts_with("extern crate ") {
        return false;
    }

    let mut rest = trimmed;
    if let Some(after_pub) = rest.strip_prefix("pub") {
        rest = after_pub.trim_start();
        if rest.starts_with(')') {
            return false;
        }
        if rest.starts_with('(') {
            let Some(close) = rest.find(')') else {
                return false;
            };
            rest = rest[close + 1..].trim_start();
        }
    }
    rest = rest.strip_prefix("unsafe ").unwrap_or(rest).trim_start();
    let Some(after_extern) = rest.strip_prefix("extern ") else {
        return false;
    };
    let after_extern = after_extern.trim_start();
    after_extern.starts_with('"') || after_extern.starts_with('{')
}

fn is_function_declaration_line(line: &str, file: &Path, line_no: usize) -> bool {
    try_parse_fn_line(line, file, line_no).is_some()
}

fn contains_rule_token(tokens: &str, token: &str) -> bool {
    let normalized = normalize_hardened_call_spacing(tokens);
    contains_rule_token_normalized(&normalized, token)
}

fn contains_rule_token_normalized(tokens: &str, token: &str) -> bool {
    match token {
        ".open(" => contains_open_options_builder_open_call_normalized(tokens),
        ".to_str().unwrap" => contains_to_str_unwrap_call_normalized(tokens),
        "let _ =" => contains_let_discard(tokens),
        "unsafe {" => tokens.contains("unsafe {") || tokens.contains("unsafe{"),
        token if token.starts_with('.') => {
            contains_method_rule_token_normalized(tokens, &normalize_hardened_call_spacing(token))
        }
        token if token.ends_with('(') || token.ends_with("()") || token.ends_with("!(") => {
            contains_rust_call_token_normalized(tokens, &normalize_hardened_call_spacing(token))
        }
        token if is_plain_identifier_token(token) => {
            contains_rust_call_token_normalized(tokens, &format!("{token}("))
        }
        token => tokens.contains(token),
    }
}

fn contains_split_line_unsafe_start(tokens: &str) -> bool {
    let normalized = normalize_hardened_call_spacing(tokens);
    let mut search_start = 0;
    while let Some(relative_idx) = normalized[search_start..].find("unsafe") {
        let idx = search_start + relative_idx;
        let before = normalized[..idx].chars().next_back();
        let after_idx = idx + "unsafe".len();
        let after = normalized[after_idx..].chars().next();
        let ident_boundary = before.map_or(true, |ch| !is_rust_ident_continue(ch))
            && after.map_or(true, |ch| !is_rust_ident_continue(ch));
        if ident_boundary {
            let after_keyword = normalized[after_idx..].trim_start();
            return !after_keyword.starts_with('{');
        }
        search_start = idx + 1;
    }
    false
}

fn contains_any_token(tokens: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| contains_rule_token(tokens, needle))
}

fn contains_hardened_create_api_call(tokens: &str) -> bool {
    let normalized = normalize_hardened_call_spacing(tokens);
    contains_rust_call_token_normalized(&normalized, "File::create(")
        || contains_rust_call_token_normalized(&normalized, "std::fs::create_dir(")
        || contains_rust_call_token_normalized(&normalized, "fs::create_dir(")
        || contains_rust_call_token_normalized(&normalized, "std::fs::create_dir_all(")
        || contains_rust_call_token_normalized(&normalized, "fs::create_dir_all(")
        || contains_open_options_create_open_call_normalized(&normalized)
}

fn normalize_hardened_call_spacing(input: &str) -> String {
    let chars: Vec<char> = input.chars().collect();
    let mut normalized = String::with_capacity(input.len());
    let mut idx = 0;

    while idx < chars.len() {
        let ch = chars[idx];
        if ch.is_whitespace() {
            let mut next_idx = idx + 1;
            while next_idx < chars.len() && chars[next_idx].is_whitespace() {
                next_idx += 1;
            }
            let prev = normalized.chars().rev().find(|candidate| !candidate.is_whitespace());
            let next = chars.get(next_idx).copied();
            if should_elide_hardened_call_space(prev, next) {
                idx = next_idx;
                continue;
            }
            if !normalized.ends_with(' ') {
                normalized.push(' ');
            }
            idx = next_idx;
            continue;
        }

        normalized.push(ch);
        idx += 1;
    }

    normalized
}

fn should_elide_hardened_call_space(prev: Option<char>, next: Option<char>) -> bool {
    matches!(prev, Some(':') | Some('.') | Some('!') | Some('('))
        || matches!(next, Some(':') | Some('.') | Some('!') | Some('(') | Some(')'))
}

fn contains_rust_call_token_normalized(tokens: &str, token: &str) -> bool {
    let mut search_start = 0;
    while let Some(relative_idx) = tokens[search_start..].find(token) {
        let idx = search_start + relative_idx;
        if rust_call_left_boundary(tokens, idx) {
            return true;
        }
        search_start = idx + 1;
    }
    false
}

fn contains_method_rule_token_normalized(tokens: &str, token: &str) -> bool {
    let mut search_start = 0;
    while let Some(relative_idx) = tokens[search_start..].find(token) {
        let idx = search_start + relative_idx;
        if idx == 0 || !tokens[..idx].ends_with('.') {
            return true;
        }
        search_start = idx + 1;
    }
    false
}

fn contains_to_str_unwrap_call_normalized(tokens: &str) -> bool {
    let mut search_start = 0;
    while let Some(relative_idx) = tokens[search_start..].find(".to_str()") {
        let idx = search_start + relative_idx;
        let after_to_str = idx + ".to_str()".len();
        if tokens[after_to_str..].starts_with(".unwrap()") {
            return true;
        }
        search_start = idx + 1;
    }
    false
}

fn contains_open_options_builder_open_call_normalized(tokens: &str) -> bool {
    open_options_builder_contexts_before_open(tokens).next().is_some()
}

fn contains_open_options_create_open_call_normalized(tokens: &str) -> bool {
    open_options_builder_contexts_before_open(tokens)
        .any(|context| builder_context_has_create_mode(context))
}

fn open_options_builder_contexts_before_open<'a>(
    tokens: &'a str,
) -> impl Iterator<Item = &'a str> + 'a {
    OpenOptionsOpenContexts { tokens, search_start: 0 }
}

struct OpenOptionsOpenContexts<'a> {
    tokens: &'a str,
    search_start: usize,
}

impl<'a> Iterator for OpenOptionsOpenContexts<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(relative_idx) = self.tokens[self.search_start..].find(".open(") {
            let open_idx = self.search_start + relative_idx;
            self.search_start = open_idx + 1;
            let context_start = self.tokens[..open_idx]
                .rfind(|ch| matches!(ch, ';' | '{' | '}'))
                .map_or(0, |idx| idx + 1);
            let context = &self.tokens[context_start..open_idx];
            if contains_rust_call_token_normalized(context, "OpenOptions::new(")
                || contains_rust_call_token_normalized(context, "File::options(")
            {
                return Some(context);
            }
        }

        None
    }
}

fn builder_context_has_create_mode(context: &str) -> bool {
    builder_method_truthy_call(context, "create")
        || builder_method_truthy_call(context, "create_new")
}

fn builder_method_truthy_call(context: &str, method: &str) -> bool {
    let needle = format!(".{method}(");
    let mut search_start = 0;
    while let Some(relative_idx) = context[search_start..].find(&needle) {
        let args_start = search_start + relative_idx + needle.len();
        let args_end =
            context[args_start..].find(')').map_or(context.len(), |idx| args_start + idx);
        if context[args_start..args_end].trim() != "false" {
            return true;
        }
        search_start = args_start;
    }

    false
}

fn contains_let_discard(tokens: &str) -> bool {
    let mut rest = tokens;
    while let Some(idx) = rest.find("let") {
        let before = &rest[..idx];
        let after_let = &rest[idx + "let".len()..];
        if before.chars().next_back().is_none_or(|ch| !is_rust_ident_continue(ch)) {
            let after_let = after_let.trim_start();
            if let Some(after_underscore) = after_let.strip_prefix('_') {
                let after_underscore = after_underscore.trim_start();
                if after_underscore.starts_with('=') {
                    return true;
                }
            }
        }
        rest = &after_let[after_let.len().min(1)..];
    }

    false
}

fn rust_call_left_boundary(tokens: &str, idx: usize) -> bool {
    idx == 0 || tokens[..idx].chars().next_back().is_none_or(|ch| !is_rust_ident_continue(ch))
}

fn is_plain_identifier_token(token: &str) -> bool {
    let mut chars = token.chars();
    chars.next().is_some_and(|ch| ch == '_' || ch.is_ascii_alphabetic())
        && chars.all(is_rust_ident_continue)
}

fn is_rust_ident_continue(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphanumeric()
}

fn trust_domain_transition(tokens: &str) -> Option<&'static str> {
    if contains_rule_token(tokens, "chroot(") {
        Some("chroot")
    } else if contains_rule_token(tokens, "setuid(") {
        Some("setuid")
    } else if contains_rule_token(tokens, "setgid(") {
        Some("setgid")
    } else {
        None
    }
}

fn module_function_name(file: &Path) -> String {
    file.file_stem().and_then(|stem| stem.to_str()).unwrap_or("module").to_string()
}

fn is_probable_call_site(trimmed: &str) -> bool {
    !(trimmed.starts_with("fn ")
        || trimmed.starts_with("pub fn ")
        || trimmed.starts_with("pub(crate) fn ")
        || trimmed.starts_with("unsafe fn ")
        || trimmed.starts_with("pub unsafe fn ")
        || trimmed.starts_with("extern fn "))
}

fn contains_any(line: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| line.contains(needle))
}

fn push_hardened_vc(
    vcs: &mut Vec<StandaloneVc>,
    file: &Path,
    line_no: usize,
    function: &str,
    kind: VcKind,
    description: &str,
) {
    vcs.push(StandaloneVc {
        function: function.to_string(),
        file: file.to_path_buf(),
        kind,
        description: format!("{}:{line_no}: {description}", file.display()),
        outcome: StandaloneOutcome::Failed,
    });
}

// ---------------------------------------------------------------------------
// Full analysis pipeline
// ---------------------------------------------------------------------------

/// Run standalone source analysis on a crate directory.
#[cfg(test)]
pub(crate) fn analyze_crate(crate_root: &Path) -> SourceAnalysisSummary {
    analyze_crate_with_options(crate_root, SourceAnalysisOptions::default())
}

/// Run standalone source analysis on a crate directory with profile options.
pub(crate) fn analyze_crate_with_options(
    crate_root: &Path,
    options: SourceAnalysisOptions,
) -> SourceAnalysisSummary {
    let files = find_source_files(crate_root);
    analyze_files_with_options(files, options)
}

/// Run standalone source analysis using an explicit Cargo manifest path.
#[cfg(test)]
pub(crate) fn analyze_crate_with_manifest_path_and_options(
    crate_root: &Path,
    manifest_path: &Path,
    options: SourceAnalysisOptions,
) -> SourceAnalysisSummary {
    let files = find_source_files_with_manifest_path(crate_root, manifest_path);
    analyze_files_with_options(files, options)
}

fn analyze_files_with_options(
    files: Vec<PathBuf>,
    options: SourceAnalysisOptions,
) -> SourceAnalysisSummary {
    let mut all_functions = Vec::new();

    for file in &files {
        all_functions.extend(extract_functions(file));
    }

    let vcs = generate_standalone_vcs_with_options(&all_functions, options);

    let present = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Present).count();
    let failed = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Failed).count();
    let unknown = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Unknown).count();

    SourceAnalysisSummary {
        files_analyzed: files.len(),
        functions_found: all_functions.len(),
        public_functions: all_functions.iter().filter(|f| f.is_public).count(),
        unsafe_functions: all_functions.iter().filter(|f| f.is_unsafe).count(),
        specified_functions: all_functions
            .iter()
            .filter(|f| f.has_requires || f.has_ensures)
            .count(),
        total_audit_rows: vcs.len(),
        present,
        failed,
        unknown,
        functions: all_functions,
        vcs,
    }
}

/// Run standalone source analysis on a single file with profile options.
pub(crate) fn analyze_file_with_options(
    file: &Path,
    options: SourceAnalysisOptions,
) -> SourceAnalysisSummary {
    let functions = extract_functions(file);
    let vcs = generate_standalone_vcs_with_options(&functions, options);

    let present = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Present).count();
    let failed = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Failed).count();
    let unknown = vcs.iter().filter(|v| v.outcome == StandaloneOutcome::Unknown).count();

    SourceAnalysisSummary {
        files_analyzed: 1,
        functions_found: functions.len(),
        public_functions: functions.iter().filter(|f| f.is_public).count(),
        unsafe_functions: functions.iter().filter(|f| f.is_unsafe).count(),
        specified_functions: functions.iter().filter(|f| f.has_requires || f.has_ensures).count(),
        total_audit_rows: vcs.len(),
        present,
        failed,
        unknown,
        functions,
        vcs,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;

    fn temp_test_dir(label: &str) -> PathBuf {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|duration| duration.as_nanos())
            .unwrap_or(0);
        std::env::temp_dir().join(format!(
            "targo_trust_source_analysis_{label}_{}_{}",
            std::process::id(),
            unique
        ))
    }

    #[test]
    fn test_extract_simple_function() {
        let source = "fn add(x: i32, y: i32) -> i32 {\n    x + y\n}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "add");
        assert!(!funcs[0].is_public);
        assert!(!funcs[0].is_unsafe);
        assert_eq!(funcs[0].line, 1);
        assert_eq!(funcs[0].params, vec!["x", "y"]);
        assert_eq!(funcs[0].return_type.as_deref(), Some("i32"));
    }

    #[test]
    fn test_extract_pub_function() {
        let source = "pub fn greet(name: &str) -> String {\n    format!(\"Hello, {name}\")\n}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].is_public);
        assert_eq!(funcs[0].name, "greet");
    }

    #[test]
    fn test_extract_pub_crate_function() {
        let source = "pub(crate) fn helper() {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].is_public);
        assert_eq!(funcs[0].name, "helper");
    }

    #[test]
    fn test_extract_unsafe_function() {
        let source = "pub unsafe fn deref_raw(ptr: *const u8) -> u8 {\n    *ptr\n}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].is_unsafe);
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_extract_async_function() {
        let source = "pub async fn fetch(url: &str) -> Result<String> {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "fetch");
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_extract_const_function() {
        let source = "const fn max(a: u32, b: u32) -> u32 {\n    if a > b { a } else { b }\n}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "max");
    }

    #[test]
    fn test_extract_with_requires() {
        let source = r#"
#[requires(x > 0)]
fn positive_only(x: i32) -> i32 {
    x
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].has_requires);
        assert!(!funcs[0].has_ensures);
    }

    #[test]
    fn test_extract_with_ensures() {
        let source = r#"
#[ensures(result > 0)]
fn always_positive() -> i32 {
    42
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(!funcs[0].has_requires);
        assert!(funcs[0].has_ensures);
    }

    #[test]
    fn test_extract_with_both_specs() {
        let source = r#"
#[requires(x > 0)]
#[ensures(result == x * 2)]
pub fn double(x: i32) -> i32 {
    x + x
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].has_requires);
        assert!(funcs[0].has_ensures);
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_extract_with_native_signature_clauses() {
        let source = r#"
pub fn double(x: i32) -> i32
    requires x > 0
    ensures result == x * 2
{
    x + x
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].has_requires);
        assert!(funcs[0].has_ensures);
        assert!(funcs[0].is_public);
        assert_eq!(funcs[0].return_type.as_deref(), Some("i32"));
    }

    #[test]
    fn test_extract_with_same_line_native_signature_clauses() {
        let source = "fn identity(x: u32) -> u32 requires x <= 10 ensures result == x { x }\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].has_requires);
        assert!(funcs[0].has_ensures);
        assert_eq!(funcs[0].return_type.as_deref(), Some("u32"));
    }

    #[test]
    fn test_extract_with_namespaced_specs() {
        let source = r#"
#[trust::requires(x > 0)]
#[trust::ensures(result == x * 2)]
pub fn double(x: i32) -> i32 {
    x + x
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].has_requires);
        assert!(funcs[0].has_ensures);
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_extract_multiline_signature_attrs_comments_and_strings() {
        let source = r##"
#[trust::requires(
    x > 0
)]
#[inline(
    always
)]
/* fn commented_out() {} */
pub unsafe extern "C" fn wrapped(
    mut x: i32,
    callback: fn(u8, u8) -> Result<(), ()>,
    items: Vec<(u8, u8)>,
) -> Result<i32, String>
where
    i32: Copy,
{
    let _text = r#"fn string_fake() {}"#;
    Ok(x)
}
"##;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "wrapped");
        assert_eq!(funcs[0].line, 9);
        assert!(funcs[0].is_public);
        assert!(funcs[0].is_unsafe);
        assert!(funcs[0].has_requires);
        assert!(!funcs[0].has_ensures);
        assert_eq!(funcs[0].params, vec!["x", "callback", "items"]);
        assert_eq!(
            funcs[0].typed_params,
            vec![
                ("x".to_string(), "i32".to_string()),
                ("callback".to_string(), "fn(u8, u8) -> Result<(), ()>".to_string()),
                ("items".to_string(), "Vec<(u8, u8)>".to_string()),
            ]
        );
        assert_eq!(funcs[0].return_type.as_deref(), Some("Result<i32, String>"));
    }

    #[test]
    fn test_extract_multiple_functions() {
        let source = r#"
fn first() {}

pub fn second() {}

#[requires(true)]
fn third() {}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 3);
        assert_eq!(funcs[0].name, "first");
        assert_eq!(funcs[1].name, "second");
        assert_eq!(funcs[2].name, "third");
        assert!(funcs[2].has_requires);
    }

    #[test]
    fn test_extract_ignores_macro_bodies_and_comment_string_fakes() {
        let source = r#"
macro_rules! make_fn {
    () => {
        pub fn generated() {}
    };
}

make_other!({
    fn macro_invocation_fake() {}
});

/* fn block_comment_fake() {} */ pub fn real() {
    let _s = "fn string_fake() {}";
}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "real");
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_extract_skips_comments() {
        let source = r#"
// fn not_a_function() {}
/* fn also_not() {} */
fn real() {}
"#;
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "real");
    }

    #[test]
    fn test_extract_self_param() {
        let source = "pub fn method(&self, x: i32) -> bool {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].params, vec!["self", "x"]);
    }

    #[test]
    fn test_extract_no_params() {
        let source = "fn empty() {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert!(funcs[0].params.is_empty());
    }

    #[test]
    fn test_extract_extern_fn() {
        let source = "pub unsafe extern \"C\" fn callback(data: *const u8) {}\n";
        let funcs = extract_functions_from_source(source, Path::new("test.rs"));
        assert_eq!(funcs.len(), 1);
        assert_eq!(funcs[0].name, "callback");
        assert!(funcs[0].is_unsafe);
        assert!(funcs[0].is_public);
    }

    #[test]
    fn test_generate_vcs_public_unspecified() {
        let funcs = vec![ParsedFunction {
            name: "foo".into(),
            file: PathBuf::from("lib.rs"),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: None,
            params: vec![],
            typed_params: vec![],
        }];
        let vcs = generate_standalone_vcs(&funcs);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].kind, VcKind::UnspecifiedPublicApi);
        assert_eq!(vcs[0].outcome, StandaloneOutcome::Unknown);
    }

    #[test]
    fn test_generate_vcs_unsafe() {
        let funcs = vec![ParsedFunction {
            name: "bar".into(),
            file: PathBuf::from("lib.rs"),
            line: 1,
            is_public: false,
            is_unsafe: true,
            has_requires: false,
            has_ensures: false,
            return_type: None,
            params: vec![],
            typed_params: vec![],
        }];
        let vcs = generate_standalone_vcs(&funcs);
        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].kind, VcKind::UnsafeFunction);
        assert_eq!(vcs[0].outcome, StandaloneOutcome::Unknown);
    }

    #[test]
    fn test_generate_vcs_specified() {
        let funcs = vec![ParsedFunction {
            name: "baz".into(),
            file: PathBuf::from("lib.rs"),
            line: 1,
            is_public: true,
            is_unsafe: false,
            has_requires: true,
            has_ensures: true,
            return_type: Some("i32".into()),
            params: vec!["x".into()],
            typed_params: vec![("x".into(), "i32".into())],
        }];
        let vcs = generate_standalone_vcs(&funcs);
        // 2 VCs: requires present + ensures present (no UnspecifiedPublicApi because has specs)
        assert_eq!(vcs.len(), 2);
        assert!(vcs.iter().any(|v| v.kind == VcKind::PreconditionPresent));
        assert!(vcs.iter().any(|v| v.kind == VcKind::PostconditionPresent));
        // Presence detection is explicitly non-proof source inventory.
        assert!(vcs.iter().all(|v| v.outcome == StandaloneOutcome::Present));
    }

    #[test]
    fn test_generate_vcs_private_no_specs() {
        let funcs = vec![ParsedFunction {
            name: "helper".into(),
            file: PathBuf::from("lib.rs"),
            line: 1,
            is_public: false,
            is_unsafe: false,
            has_requires: false,
            has_ensures: false,
            return_type: None,
            params: vec![],
            typed_params: vec![],
        }];
        let vcs = generate_standalone_vcs(&funcs);
        // Private function with no specs and not unsafe generates no VCs
        assert!(vcs.is_empty());
    }

    #[test]
    fn test_hardened_source_analysis_flags_path_bytes_and_errors() {
        let source = r#"
pub fn install(path: &std::path::Path, bytes: &[u8]) {
    std::fs::remove_file(path).ok();
    let _ = String::from_utf8_lossy(bytes);
}
"#;
        let file = Path::new("hardened.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedRawPathApi));
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedErrorDiscard));
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedByteLoss));
        assert!(vcs.iter().all(|vc| vc.outcome == StandaloneOutcome::Failed));
    }

    #[test]
    fn test_hardened_source_analysis_flags_permission_and_trust_ordering() {
        let source = r#"
pub fn configure(path: &std::path::Path) {
    std::fs::create_dir(path).unwrap();
    std::fs::set_permissions(path, todo!()).unwrap();
}

pub fn enter(root: &std::path::Path) {
    chroot(root);
    get_user_by_name("nobody");
}
"#;
        let file = Path::new("profile.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedPermissionWindow));
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedPermissionCreate));
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedPermissionChange));
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedTrustBoundary));
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedTrustDomainOrder));
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedPanic));
    }

    #[test]
    fn test_hardened_source_analysis_flags_identity_and_ffi() {
        let source = r#"
pub fn identify(path: &std::path::Path) {
    let _root = path == std::path::Path::new("/");
    let _ = std::fs::canonicalize(path);
}

extern "C-unwind" {
    fn getenv(name: *const std::os::raw::c_char) -> *mut std::os::raw::c_char;
}

pub fn ffi_boundary() {
    unsafe {
        let _ = 1;
    }
}
"#;
        let file = Path::new("identity_ffi.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedPathIdentity));
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedFfiBoundary));
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedUnsafeOperation));
    }

    #[test]
    fn test_hardened_source_analysis_does_not_attribute_post_function_items_to_previous_function() {
        let source = r#"
pub fn trust_domain_ordering_boundary(root: &std::ffi::OsStr) {
    chroot(root);
}

extern "C" {
    fn getenv(name: *const std::os::raw::c_char) -> *mut std::os::raw::c_char;
}

pub fn unsafe_ffi_boundary() {
    unsafe {
        let _ = 1;
    }
}
"#;
        let file = Path::new("scope_boundary.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(!vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedFfiBoundary
                && vc.function == "trust_domain_ordering_boundary"
                && vc.description.contains("extern boundary")
        }));
        assert!(vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedFfiBoundary
                && vc.function == "scope_boundary"
                && vc.description.contains("extern boundary")
        }));
        assert!(vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedUnsafeOperation
                && vc.function == "unsafe_ffi_boundary"
                && vc.description.contains("trusted-wrapper")
        }));
    }

    #[test]
    fn test_hardened_source_analysis_does_not_attribute_same_line_post_function_items_to_previous_function()
     {
        let source = r#"
pub fn trust_domain_ordering_boundary(root: &std::ffi::OsStr) { chroot(root); } extern "C" {
    fn getenv(name: *const std::os::raw::c_char) -> *mut std::os::raw::c_char;
}
"#;
        let file = Path::new("same_line_scope_boundary.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(!vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedFfiBoundary
                && vc.function == "trust_domain_ordering_boundary"
                && vc.description.contains("extern boundary")
        }));
        assert!(vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedFfiBoundary
                && vc.function == "same_line_scope_boundary"
                && vc.description.contains("extern boundary")
        }));
    }

    #[test]
    fn test_hardened_source_analysis_scans_one_line_function_bodies() {
        let source = r#"
pub fn one_line(path: &std::path::Path) { std::fs::remove_file(path).unwrap(); unsafe { let _ = path.as_os_str(); } }
"#;
        let file = Path::new("one_line.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(
            vcs.iter()
                .any(|vc| { vc.kind == VcKind::HardenedRawPathApi && vc.function == "one_line" })
        );
        assert!(
            vcs.iter().any(|vc| {
                vc.kind == VcKind::HardenedUnsafeOperation && vc.function == "one_line"
            })
        );
    }

    #[test]
    fn test_hardened_source_analysis_flags_split_line_unsafe_blocks() {
        let source = r#"
pub fn split_unsafe() {
    unsafe
    {
        let _ = 1;
    }
}
"#;
        let file = Path::new("split_unsafe.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedUnsafeOperation && vc.function == "split_unsafe"
        }));
    }

    #[test]
    fn test_hardened_source_analysis_flags_default_abi_extern_blocks() {
        let source = r#"
unsafe extern {
    fn getpid() -> i32;
}
"#;
        let file = Path::new("default_abi.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedFfiBoundary
                && vc.function == "default_abi"
                && vc.description.contains("extern boundary")
        }));
    }

    #[test]
    fn test_hardened_source_analysis_filters_declarations_comments_and_strings() {
        let source = r#"
pub(crate) unsafe fn chroot(_path: &std::path::Path);
pub(super) fn get_user_by_name(_name: &str) {}

pub fn clean() {
    let _text = "std::fs::remove_file(path) // chroot(root)";
    /* std::fs::set_permissions(path, todo!()).unwrap(); */
}

pub fn process() {
    setuid(0);
    getpwnam("root");
    std::io::stdout();
}
"#;
        let file = Path::new("declarations.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(
            vcs.iter()
                .any(|vc| vc.kind == VcKind::HardenedTrustDomainOrder && vc.function == "process")
        );
        assert!(
            vcs.iter()
                .any(|vc| vc.kind == VcKind::HardenedProcessSemantics && vc.function == "process")
        );
        assert!(
            !vcs.iter().any(|vc| vc.kind == VcKind::HardenedRawPathApi && vc.function == "clean")
        );
        assert!(
            !vcs.iter()
                .any(|vc| vc.kind == VcKind::HardenedTrustBoundary && vc.function == "chroot")
        );
    }

    #[test]
    fn test_hardened_source_analysis_matches_spaced_calls_without_suffix_wrappers() {
        let source = r#"
pub fn spaced(path: &std::path::Path) {
    std :: fs :: remove_file (path);
    std :: fs :: File :: create (path);
    panic ! ("bad");
}

pub fn wrappers(path: &std::path::Path) {
    myfs::remove_file(path);
    SafeFile::create(path);
}
"#;
        let file = Path::new("spaced.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(
            vcs.iter().any(|vc| vc.kind == VcKind::HardenedRawPathApi && vc.function == "spaced")
        );
        assert!(vcs.iter().any(|vc| vc.kind == VcKind::HardenedPanic && vc.function == "spaced"));
        assert!(
            !vcs.iter()
                .any(|vc| vc.kind == VcKind::HardenedRawPathApi && vc.function == "wrappers")
        );
    }

    #[test]
    fn test_hardened_source_analysis_limits_open_method_to_file_builders() {
        let source = r#"
pub fn open_methods(path: &std::path::Path, socket: &mut Socket) {
    socket.open(path);
    std::fs::OpenOptions::new().read(true).open(path);
    std :: fs :: File :: options () . write (true) . open (path);
}
"#;
        let file = Path::new("open_methods.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);
        let raw_path_count = vcs
            .iter()
            .filter(|vc| vc.kind == VcKind::HardenedRawPathApi && vc.function == "open_methods")
            .count();

        assert_eq!(raw_path_count, 2);
    }

    #[test]
    fn test_hardened_source_analysis_permission_window_uses_actual_create_calls() {
        let source = r#"
pub fn read_then_chmod(path: &std::path::Path) {
    std::fs::File::open(path).unwrap();
    std::fs::OpenOptions::new().read(true).open(path).unwrap();
    std::fs::set_permissions(path, todo!()).unwrap();
}

pub fn open_create_false_then_chmod(path: &std::path::Path) {
    std::fs::OpenOptions::new().create(false).open(path).unwrap();
    std::fs::set_permissions(path, todo!()).unwrap();
}

pub fn open_create_then_chmod(path: &std::path::Path) {
    std::fs::OpenOptions::new().create(true).write(true).open(path).unwrap();
    std::fs::set_permissions(path, todo!()).unwrap();
}

pub fn file_create_then_chmod(path: &std::path::Path) {
    std :: fs :: File :: create (path).unwrap();
    std::fs::set_permissions(path, todo!()).unwrap();
}
"#;
        let file = Path::new("permission_window.rs");
        let funcs = extract_functions_from_source(source, file);
        let func_refs: Vec<&ParsedFunction> = funcs.iter().collect();
        let vcs = generate_hardened_source_vcs_from_source(source, file, &func_refs);

        assert!(!vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedPermissionWindow && vc.function == "read_then_chmod"
        }));
        assert!(!vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedPermissionWindow
                && vc.function == "open_create_false_then_chmod"
        }));
        assert!(vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedPermissionWindow && vc.function == "open_create_then_chmod"
        }));
        assert!(vcs.iter().any(|vc| {
            vc.kind == VcKind::HardenedPermissionWindow && vc.function == "file_create_then_chmod"
        }));
    }

    #[test]
    fn test_analyze_crate_with_temp_dir() {
        let dir = std::env::temp_dir().join("targo_trust_test_analyze");
        let src_dir = dir.join("src");
        let _ = std::fs::create_dir_all(&src_dir);
        std::fs::write(
            src_dir.join("lib.rs"),
            r#"
pub fn add(x: i32, y: i32) -> i32 { x + y }

#[requires(n > 0)]
pub fn checked(n: u32) -> u32 { n }

unsafe fn raw() {}
"#,
        )
        .expect("write test file");

        let summary = analyze_crate(&dir);
        assert_eq!(summary.files_analyzed, 1);
        assert_eq!(summary.functions_found, 3);
        assert_eq!(summary.public_functions, 2);
        assert_eq!(summary.unsafe_functions, 1);
        assert_eq!(summary.specified_functions, 1);
        assert!(summary.total_audit_rows > 0);

        // Cleanup
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_no_src_dir() {
        let files = find_source_files(Path::new("/nonexistent/path"));
        assert!(files.is_empty());
    }

    #[test]
    fn test_find_source_files_uses_input_root_without_process_manifest_override() {
        let dir = temp_test_dir("deterministic-root");
        let alt_dir = dir.join("alt");
        std::fs::create_dir_all(dir.join("src")).expect("should create root src");
        std::fs::create_dir_all(alt_dir.join("src")).expect("should create alt src");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "deterministic-root"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write root Cargo.toml");
        std::fs::write(
            alt_dir.join("Cargo.toml"),
            r#"
[package]
name = "deterministic-alt"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write alt Cargo.toml");
        std::fs::write(dir.join("src/lib.rs"), "pub fn root_fn() {}\n")
            .expect("should write root lib");
        std::fs::write(alt_dir.join("src/lib.rs"), "pub fn alt_fn() {}\n")
            .expect("should write alt lib");

        let default_files = find_source_files(&dir);
        assert_eq!(default_files, vec![dir.join("src/lib.rs")]);

        let explicit_files =
            find_source_files_with_manifest_path(&dir, Path::new("alt/Cargo.toml"));
        assert_eq!(explicit_files, vec![alt_dir.join("src/lib.rs")]);

        let summary = analyze_crate_with_manifest_path_and_options(
            &dir,
            Path::new("alt/Cargo.toml"),
            SourceAnalysisOptions::default(),
        );
        assert_eq!(summary.files_analyzed, 1);
        assert_eq!(summary.functions_found, 1);
        assert_eq!(summary.functions[0].name, "alt_fn");

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_honors_custom_lib_path() {
        let dir = temp_test_dir("custom-lib");
        let crate_dir = dir.join("crate_root");
        std::fs::create_dir_all(&crate_dir).expect("should create custom lib dir");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "custom-lib"
version = "0.1.0"
edition = "2021"

[lib]
path = "crate_root/lib.rs"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(
            crate_dir.join("lib.rs"),
            r#"
mod helper;

pub fn entry() {}
"#,
        )
        .expect("should write lib.rs");
        std::fs::write(crate_dir.join("helper.rs"), "pub fn helper() {}\n")
            .expect("should write helper.rs");

        let files = find_source_files(&dir);
        assert_eq!(files.len(), 2);
        assert!(files.contains(&crate_dir.join("lib.rs")));
        assert!(files.contains(&crate_dir.join("helper.rs")));

        let summary = analyze_crate(&dir);
        assert_eq!(summary.files_analyzed, 2);
        assert_eq!(summary.functions_found, 2);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_honors_custom_bin_path_without_autobins() {
        let dir = temp_test_dir("custom-bin");
        let custom_bin_dir = dir.join("tools");
        let src_bin_dir = dir.join("src/bin/ignored");
        std::fs::create_dir_all(&custom_bin_dir).expect("should create custom bin dir");
        std::fs::create_dir_all(&src_bin_dir).expect("should create src bin dir");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "custom-bin"
version = "0.1.0"
edition = "2021"
autobins = false

[[bin]]
name = "custom-bin"
path = "tools/custom_main.rs"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(custom_bin_dir.join("custom_main.rs"), "pub fn custom_main() {}\n")
            .expect("should write custom bin");
        std::fs::write(custom_bin_dir.join("helper.rs"), "pub fn helper() {}\n")
            .expect("should write custom bin helper");
        std::fs::write(dir.join("src/bin/ignored/main.rs"), "pub fn ignored() {}\n")
            .expect("should write ignored auto bin");

        let files = find_source_files(&dir);
        assert_eq!(
            files,
            vec![custom_bin_dir.join("custom_main.rs"), custom_bin_dir.join("helper.rs")]
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_auto_bin_includes_nested_helper_module() {
        let dir = temp_test_dir("auto-bin-helper-module");
        std::fs::create_dir_all(dir.join("src/bin/common")).expect("should create helper dir");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "auto-bin-helper-module"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(dir.join("src/bin/tool.rs"), "mod common;\nfn main() {}\n")
            .expect("should write auto bin");
        std::fs::write(dir.join("src/bin/common/mod.rs"), "pub fn helper() {}\n")
            .expect("should write nested helper module");

        let files = find_source_files(&dir);
        assert!(files.contains(&dir.join("src/bin/tool.rs")), "missing auto bin: {files:?}");
        assert!(
            files.contains(&dir.join("src/bin/common/mod.rs")),
            "missing nested auto bin helper module: {files:?}"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_includes_examples_tests_and_benches() {
        let dir = temp_test_dir("examples-tests-benches");
        for path in [
            "manual_examples",
            "manual_tests",
            "manual_benches",
            "examples/grouped",
            "tests/common",
            "tests/explicit_nested",
            "tests/grouped",
            "benches/common",
            "benches/explicit_nested",
            "benches/grouped",
        ] {
            std::fs::create_dir_all(dir.join(path)).expect("should create target dir");
        }
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "target-kinds"
version = "0.1.0"
edition = "2021"

[[example]]
name = "manual-example"
path = "manual_examples/example_entry.rs"

[[test]]
name = "manual-test"
path = "manual_tests/integration_entry.rs"

[[test]]
name = "manual-nested-test"
path = "tests/explicit_nested/main.rs"

[[bench]]
name = "manual-bench"
path = "manual_benches/bench_entry.rs"

[[bench]]
name = "manual-nested-bench"
path = "benches/explicit_nested/main.rs"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(
            dir.join("manual_examples/example_entry.rs"),
            "pub fn manual_example() {}\n",
        )
        .expect("should write manual example");
        std::fs::write(
            dir.join("manual_examples/helper.rs"),
            "pub fn manual_example_helper() {}\n",
        )
        .expect("should write manual example helper");
        std::fs::write(dir.join("manual_tests/integration_entry.rs"), "pub fn manual_test() {}\n")
            .expect("should write manual test");
        std::fs::write(dir.join("manual_benches/bench_entry.rs"), "pub fn manual_bench() {}\n")
            .expect("should write manual bench");
        std::fs::write(dir.join("examples/auto.rs"), "pub fn auto_example() {}\n")
            .expect("should write auto example");
        std::fs::write(dir.join("examples/grouped/main.rs"), "pub fn grouped_example() {}\n")
            .expect("should write grouped example");
        std::fs::write(dir.join("examples/grouped/helper.rs"), "pub fn grouped_helper() {}\n")
            .expect("should write grouped example helper");
        std::fs::write(dir.join("tests/auto_test.rs"), "pub fn auto_test() {}\n")
            .expect("should write auto test");
        std::fs::write(dir.join("tests/common/mod.rs"), "pub fn test_helper() {}\n")
            .expect("should write test helper module");
        std::fs::write(
            dir.join("tests/explicit_nested/main.rs"),
            "pub fn explicit_nested_test() {}\n",
        )
        .expect("should write explicit nested test");
        std::fs::write(dir.join("tests/grouped/main.rs"), "pub fn ignored_test_dir() {}\n")
            .expect("should write ignored grouped test");
        std::fs::write(dir.join("benches/auto_bench.rs"), "pub fn auto_bench() {}\n")
            .expect("should write auto bench");
        std::fs::write(dir.join("benches/common/mod.rs"), "pub fn bench_helper() {}\n")
            .expect("should write bench helper module");
        std::fs::write(
            dir.join("benches/explicit_nested/main.rs"),
            "pub fn explicit_nested_bench() {}\n",
        )
        .expect("should write explicit nested bench");
        std::fs::write(dir.join("benches/grouped/main.rs"), "pub fn ignored_bench_dir() {}\n")
            .expect("should write ignored grouped bench");

        let files = find_source_files(&dir);
        for expected in [
            "manual_examples/example_entry.rs",
            "manual_examples/helper.rs",
            "manual_tests/integration_entry.rs",
            "manual_benches/bench_entry.rs",
            "examples/auto.rs",
            "examples/grouped/main.rs",
            "examples/grouped/helper.rs",
            "tests/auto_test.rs",
            "tests/common/mod.rs",
            "tests/explicit_nested/main.rs",
            "benches/auto_bench.rs",
            "benches/common/mod.rs",
            "benches/explicit_nested/main.rs",
        ] {
            assert!(files.contains(&dir.join(expected)), "missing {expected}: {files:?}");
        }
        for unexpected in ["tests/grouped/main.rs", "benches/grouped/main.rs"] {
            assert!(
                !files.contains(&dir.join(unexpected)),
                "auto tests/benches should not recursively collect {unexpected}: {files:?}"
            );
        }

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_walks_up_to_manifest_ancestor() {
        let dir = temp_test_dir("ancestor");
        let nested = dir.join("src/nested/deeper");
        std::fs::create_dir_all(&nested).expect("should create nested dir");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "ancestor"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(dir.join("src/lib.rs"), "pub fn from_root() {}\n")
            .expect("should write lib.rs");
        std::fs::write(dir.join("src/nested/mod.rs"), "pub fn nested() {}\n")
            .expect("should write nested module");

        let files = find_source_files(&nested);
        assert!(files.contains(&dir.join("src/lib.rs")));
        assert!(files.contains(&dir.join("src/nested/mod.rs")));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_accepts_manifest_path_input() {
        let dir = temp_test_dir("manifest-input");
        std::fs::create_dir_all(dir.join("src")).expect("should create src dir");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "manifest-input"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(dir.join("src/lib.rs"), "pub fn lib_fn() {}\n")
            .expect("should write lib.rs");

        let files = find_source_files(&dir.join("Cargo.toml"));
        assert_eq!(files, vec![dir.join("src/lib.rs")]);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_find_source_files_does_not_follow_symlinked_dirs() {
        let dir = temp_test_dir("symlink-no-follow");
        let src_dir = dir.join("src");
        let outside_dir = dir.join("outside");
        std::fs::create_dir_all(&src_dir).expect("should create src dir");
        std::fs::create_dir_all(&outside_dir).expect("should create outside dir");
        std::fs::write(src_dir.join("lib.rs"), "pub fn real() {}\n").expect("should write lib.rs");
        std::fs::write(outside_dir.join("linked.rs"), "pub fn linked() {}\n")
            .expect("should write linked file");
        std::os::unix::fs::symlink(&outside_dir, src_dir.join("linked"))
            .expect("should create symlinked dir");

        let files = find_source_files(&dir);
        assert_eq!(files, vec![src_dir.join("lib.rs")]);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_find_source_files_rejects_manifest_targets_through_symlinked_parent() {
        let dir = temp_test_dir("manifest-target-symlink-parent");
        let outside_dir = dir.join("outside");
        std::fs::create_dir_all(&outside_dir).expect("should create outside dir");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[package]
name = "manifest-target-symlink-parent"
version = "0.1.0"
edition = "2021"

[lib]
path = "linked/lib.rs"
"#,
        )
        .expect("should write Cargo.toml");
        std::fs::write(outside_dir.join("lib.rs"), "pub fn linked() {}\n")
            .expect("should write outside lib");
        std::os::unix::fs::symlink(&outside_dir, dir.join("linked"))
            .expect("should create symlinked target parent");

        let files = find_source_files(&dir);
        assert!(files.is_empty());

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_supports_workspace_member_glob() {
        let dir = temp_test_dir("workspace");
        let member_a = dir.join("crates/a/src");
        let member_b = dir.join("crates/b/src");
        std::fs::create_dir_all(&member_a).expect("should create member a");
        std::fs::create_dir_all(&member_b).expect("should create member b");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[workspace]
members = ["crates/*"]
"#,
        )
        .expect("should write workspace Cargo.toml");
        std::fs::write(
            dir.join("crates/a/Cargo.toml"),
            r#"
[package]
name = "member-a"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write member a Cargo.toml");
        std::fs::write(
            dir.join("crates/b/Cargo.toml"),
            r#"
[package]
name = "member-b"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write member b Cargo.toml");
        std::fs::write(member_a.join("lib.rs"), "pub fn member_a() {}\n")
            .expect("should write member a lib");
        std::fs::write(member_b.join("main.rs"), "pub fn member_b() {}\n")
            .expect("should write member b main");

        let files = find_source_files(&dir);
        assert!(files.contains(&dir.join("crates/a/src/lib.rs")));
        assert!(files.contains(&dir.join("crates/b/src/main.rs")));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_workspace_default_members_limit_discovery() {
        let dir = temp_test_dir("workspace-default-members");
        let member_a = dir.join("crates/a/src");
        let member_b = dir.join("crates/b/src");
        std::fs::create_dir_all(&member_a).expect("should create member a");
        std::fs::create_dir_all(&member_b).expect("should create member b");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[workspace]
members = ["crates/*"]
default-members = ["crates/a", "crates/b"]
exclude = ["crates/a"]
"#,
        )
        .expect("should write workspace Cargo.toml");
        std::fs::write(
            dir.join("crates/a/Cargo.toml"),
            r#"
[package]
name = "member-a"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write member a Cargo.toml");
        std::fs::write(
            dir.join("crates/b/Cargo.toml"),
            r#"
[package]
name = "member-b"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write member b Cargo.toml");
        std::fs::write(member_a.join("lib.rs"), "pub fn member_a() {}\n")
            .expect("should write member a lib");
        std::fs::write(member_b.join("lib.rs"), "pub fn member_b() {}\n")
            .expect("should write member b lib");

        let files = find_source_files(&dir);
        assert_eq!(files, vec![dir.join("crates/b/src/lib.rs")]);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_find_source_files_explicit_relative_manifest_honors_workspace_exclude() {
        let dir = temp_test_dir("workspace-exclude-explicit-manifest");
        let workspace_dir = dir.join("workspace");
        let member_a = workspace_dir.join("crates/a/src");
        let member_b = workspace_dir.join("crates/b/src");
        std::fs::create_dir_all(&member_a).expect("should create member a");
        std::fs::create_dir_all(&member_b).expect("should create member b");
        std::fs::write(
            workspace_dir.join("Cargo.toml"),
            r#"
[workspace]
members = ["crates/*"]
exclude = ["crates/b"]
"#,
        )
        .expect("should write workspace Cargo.toml");
        std::fs::write(
            workspace_dir.join("crates/a/Cargo.toml"),
            r#"
[package]
name = "member-a"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write member a Cargo.toml");
        std::fs::write(
            workspace_dir.join("crates/b/Cargo.toml"),
            r#"
[package]
name = "member-b"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write member b Cargo.toml");
        std::fs::write(member_a.join("lib.rs"), "pub fn member_a() {}\n")
            .expect("should write member a lib");
        std::fs::write(member_b.join("lib.rs"), "pub fn member_b() {}\n")
            .expect("should write member b lib");

        let files = find_source_files_with_manifest_path(&dir, Path::new("workspace/Cargo.toml"));
        assert_eq!(files, vec![workspace_dir.join("crates/a/src/lib.rs")]);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn test_find_source_files_workspace_glob_does_not_follow_symlinked_members() {
        let dir = temp_test_dir("workspace-symlink-no-follow");
        let real_member = dir.join("crates/real/src");
        let outside_member = dir.join("outside-member/src");
        std::fs::create_dir_all(&real_member).expect("should create real member");
        std::fs::create_dir_all(&outside_member).expect("should create outside member");
        std::fs::write(
            dir.join("Cargo.toml"),
            r#"
[workspace]
members = ["crates/*"]
"#,
        )
        .expect("should write workspace Cargo.toml");
        std::fs::write(
            dir.join("crates/real/Cargo.toml"),
            r#"
[package]
name = "real-member"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write real member Cargo.toml");
        std::fs::write(
            dir.join("outside-member/Cargo.toml"),
            r#"
[package]
name = "outside-member"
version = "0.1.0"
edition = "2021"
"#,
        )
        .expect("should write outside member Cargo.toml");
        std::fs::write(real_member.join("lib.rs"), "pub fn real() {}\n")
            .expect("should write real lib");
        std::fs::write(outside_member.join("lib.rs"), "pub fn leaked() {}\n")
            .expect("should write linked lib");
        std::os::unix::fs::symlink(dir.join("outside-member"), dir.join("crates/linked"))
            .expect("should create symlinked workspace member");

        let files = find_source_files(&dir);
        assert_eq!(files, vec![dir.join("crates/real/src/lib.rs")]);

        let _ = std::fs::remove_dir_all(&dir);
    }
}
