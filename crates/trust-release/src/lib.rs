//! Release-gate primitives for Trust evidence checks.
//!
//! This crate intentionally keeps the first gates small and dependency-free so
//! `targo-trust` can call the same logic later without inheriting CLI policy.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::{fmt, fs, io};

use serde::{Deserialize, Serialize};

/// Overall status for one gate or an aggregate of gates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GateStatus {
    Pass,
    Warn,
    Blocked,
    Fail,
}

impl GateStatus {
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Self::Fail, _) | (_, Self::Fail) => Self::Fail,
            (Self::Blocked, _) | (_, Self::Blocked) => Self::Blocked,
            (Self::Warn, _) | (_, Self::Warn) => Self::Warn,
            (Self::Pass, Self::Pass) => Self::Pass,
        }
    }
}

/// Process-exit class a future CLI can map to concrete numeric exits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExitCodeKind {
    Success,
    WarningsOnly,
    MissingEvidence,
    ReleaseBlocked,
}

impl ExitCodeKind {
    pub fn as_i32(self) -> i32 {
        match self {
            Self::Success => 0,
            Self::WarningsOnly => 0,
            Self::MissingEvidence => 1,
            Self::ReleaseBlocked => 1,
        }
    }
}

/// Severity for a single finding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FindingSeverity {
    Warning,
    Blocker,
    Error,
}

/// Optional source location for text/file-backed findings.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GateLocation {
    pub path: String,
    pub line: usize,
}

impl GateLocation {
    pub fn new(path: impl Into<String>, line: usize) -> Self {
        Self { path: path.into(), line }
    }
}

/// One actionable gate finding.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GateFinding {
    pub severity: FindingSeverity,
    pub code: String,
    pub message: String,
    pub location: Option<GateLocation>,
    pub text: Option<String>,
}

impl GateFinding {
    pub fn error(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: FindingSeverity::Error,
            code: code.into(),
            message: message.into(),
            location: None,
            text: None,
        }
    }

    pub fn warning(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: FindingSeverity::Warning,
            code: code.into(),
            message: message.into(),
            location: None,
            text: None,
        }
    }

    pub fn blocker(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            severity: FindingSeverity::Blocker,
            code: code.into(),
            message: message.into(),
            location: None,
            text: None,
        }
    }

    pub fn with_location(mut self, path: impl Into<String>, line: usize) -> Self {
        self.location = Some(GateLocation::new(path, line));
        self
    }

    pub fn with_text(mut self, text: impl Into<String>) -> Self {
        self.text = Some(text.into());
        self
    }
}

/// Result for one named release gate.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GateReport {
    pub gate: String,
    pub status: GateStatus,
    pub release_critical: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub evidence_refs: Vec<String>,
    pub findings: Vec<GateFinding>,
}

impl GateReport {
    pub fn new(gate: impl Into<String>, findings: Vec<GateFinding>) -> Self {
        let status = findings.iter().fold(GateStatus::Pass, |status, finding| {
            status.combine(match finding.severity {
                FindingSeverity::Warning => GateStatus::Warn,
                FindingSeverity::Blocker => GateStatus::Blocked,
                FindingSeverity::Error => GateStatus::Fail,
            })
        });

        Self {
            gate: gate.into(),
            status,
            release_critical: true,
            evidence_refs: Vec::new(),
            findings,
        }
    }

    pub fn pass(gate: impl Into<String>) -> Self {
        Self {
            gate: gate.into(),
            status: GateStatus::Pass,
            release_critical: true,
            evidence_refs: Vec::new(),
            findings: Vec::new(),
        }
    }

    pub fn with_evidence_refs<I, S>(mut self, refs: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.evidence_refs = refs.into_iter().map(Into::into).collect();
        self
    }

    pub fn with_release_critical(mut self, release_critical: bool) -> Self {
        self.release_critical = release_critical;
        self
    }

    pub fn exit_code_kind(&self) -> ExitCodeKind {
        match self.status {
            GateStatus::Pass => ExitCodeKind::Success,
            GateStatus::Warn => ExitCodeKind::WarningsOnly,
            GateStatus::Blocked => ExitCodeKind::MissingEvidence,
            GateStatus::Fail => ExitCodeKind::ReleaseBlocked,
        }
    }
}

/// Combined report over multiple gates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AggregateReport {
    pub reports: Vec<GateReport>,
}

impl AggregateReport {
    pub fn new(reports: Vec<GateReport>) -> Self {
        Self { reports }
    }

    pub fn status(&self) -> GateStatus {
        self.reports.iter().fold(GateStatus::Pass, |status, report| status.combine(report.status))
    }

    pub fn exit_code_kind(&self) -> ExitCodeKind {
        match self.status() {
            GateStatus::Pass => ExitCodeKind::Success,
            GateStatus::Warn => ExitCodeKind::WarningsOnly,
            GateStatus::Blocked => ExitCodeKind::MissingEvidence,
            GateStatus::Fail => ExitCodeKind::ReleaseBlocked,
        }
    }
}

/// Evidence profile that controls fail-closed vs metadata/local behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EvidenceProfile {
    Public,
    Release,
    Metadata,
    Local,
}

impl EvidenceProfile {
    fn blocks_unreleased_owned_deps(self) -> bool {
        matches!(self, Self::Public | Self::Release)
    }

    fn reports_unreleased_owned_deps(self) -> bool {
        !matches!(self, Self::Local)
    }
}

const DEFAULT_TOOL_NAME_EVIDENCE_PATHS: &[&str] = &[
    "src/version",
    "designs/2026-04-29-trust-first-release-cli-and-trust-versioning.md",
    "designs/2026-04-30-trust-first-release-cli-execution-plan.md",
    "scripts/build.sh",
    "scripts/record_full_verify_transcript.sh",
    "scripts/stage2_noverify_self_build.sh",
    "scripts/dev-test.sh",
    "tests/test_owned_dependency_sources.py",
    "targo-trust/src/cargo_cache_materialization_cli.rs",
    "targo-trust/src/release_cli/mod.rs",
    "targo-trust/src/release_cli/gates.rs",
    "targo-trust/src/release_cli/product_proof.rs",
    "targo-trust/src/rust_vs_trust.rs",
    "targo-trust/src/script_cli.rs",
    "targo-trust/src/self_verify_cli.rs",
    "targo-trust/tests/hardened_cli.rs",
    "targo-trust/tests/program_index_benchmark_cli.rs",
    "targo-trust/tests/release_cli.rs",
    "targo-trust/tests/rust_vs_trust_cli.rs",
    "targo-trust/tests/version_cli.rs",
    "crates/trust-integration-tests/tests/compat_check.rs",
    "crates/trust-integration-tests/tests/real_ay_verification.rs",
    "docs/install.md",
    "docs/USING_TRUST.md",
    "docs/toolchain-replacement-checklist.md",
    "docs/release-gate-checklist.md",
    "docs/testing-strategy.md",
    "docs/publication-v3-release-gate.md",
    "docs/public-distribution.md",
    "docs/cli-reference.md",
    "tests/e2e_verify_suite.sh",
    "tests/e2e_full_verifier_three_suite_sample.sh",
    "tests/e2e_binary_decompilation_golden_json.sh",
    "tests/e2e_aarch64_decomp_json_gate.sh",
    "tests/fixtures/binary_decomp/x86_64_provenance_parity.sh",
    "tests/run_trust_superset_suite.sh",
    "docs/trust-naming.md",
];

/// Return the checked-in release evidence paths covered by the `tool-names` gate.
pub fn default_tool_name_evidence_paths(root: &Path) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = DEFAULT_TOOL_NAME_EVIDENCE_PATHS
        .iter()
        .map(|relative| root.join(relative))
        .filter(|path| path.is_file())
        .collect();

    let e2e_dir = root.join("tests");
    if let Ok(entries) = fs::read_dir(e2e_dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
                continue;
            };
            if path.is_file() && name.starts_with("e2e_") && name.ends_with(".sh") {
                paths.push(path);
            }
        }
    }

    paths.sort();
    paths.dedup();
    paths
}

/// Check release evidence text for ambiguous Trust cargo/rustc wording.
pub fn check_tool_names_text(path: impl AsRef<str>, text: &str) -> GateReport {
    let path = path.as_ref();
    let mut findings = Vec::new();

    for (line_index, line) in text.lines().enumerate() {
        let line_number = line_index + 1;
        let trimmed = line.trim();

        if contains_word(line, "TRUST_CARGO")
            || contains_word(line, "TRUST_CARGO_BIN")
            || contains_word(line, "TRUST_CARGO_CMD")
            || contains_word(line, "TRUST_CARGO_LABEL")
        {
            findings.push(
                GateFinding::error(
                    "trust-cargo-env",
                    "Trust Cargo variables in release evidence should use TRUST_TARGO_* names",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_trust_targo_bin_as_cargo(line) {
            findings.push(
                GateFinding::error(
                    "trust-targo-bin-cargo",
                    "TRUST_TARGO_BIN must point at a binary named targo, not an upstream cargo compatibility alias", // Trust: produced frontend binary is targo
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if contains_word(line, "TRUST_RUSTC_BIN")
            || contains_word(line, "TRUST_RUSTC_CMD")
            || contains_word(line, "TRUST_RUSTC_LABEL")
        {
            findings.push(
                GateFinding::error(
                    "trust-rustc-env",
                    "Trust compiler variables in release evidence should use TRUST_TRUSTC_* names",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_bare_tool_command(line, "cargo") && !allowed_tool_context(line) {
            findings.push(
                GateFinding::error(
                    "bare-cargo-command",
                    "Bare cargo commands in Trust evidence/docs should be targo or explicitly labeled as host/upstream/internal only",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_bare_tool_command(line, "rustc") && !allowed_tool_context(line) {
            findings.push(
                GateFinding::error(
                    "bare-rustc-command",
                    "Bare rustc commands in Trust evidence/docs should be trustc or explicitly labeled as host/upstream/internal only",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_ambiguous_trust_tool_reference(line, "cargo") && !allowed_tool_context(line) {
            findings.push(
                GateFinding::error(
                    "ambiguous-trust-cargo",
                    "Trust-owned Cargo references should say targo or explicitly label cargo as host/upstream/internal only",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_ambiguous_trust_tool_reference(line, "rustc") && !allowed_tool_context(line) {
            findings.push(
                GateFinding::error(
                    "ambiguous-trust-rustc",
                    "Trust-owned compiler references should say trustc or explicitly label rustc as host/upstream/internal only",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_trust_tool_phrase(line, "cargo")
            && !has_rustup_trust_tool(line, "cargo")
            && !allowed_tool_context(line)
        {
            findings.push(
                GateFinding::error(
                    "trust-cargo-phrase",
                    "Trust Cargo evidence should name the executable as targo",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_trust_tool_phrase(line, "rustc")
            && !has_rustup_trust_tool(line, "rustc")
            && !allowed_tool_context(line)
        {
            findings.push(
                GateFinding::error(
                    "trust-rustc-phrase",
                    "Trust compiler evidence should name the executable as trustc",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_rustup_trust_tool(line, "cargo") {
            findings.push(
                GateFinding::error(
                    "rustup-trust-cargo",
                    "Use canonical targo from the selected Trust sysroot; rustup may only be selector convenience after proving that sysroot; rustup run trust cargo is not release evidence",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_rustup_trust_tool(line, "rustc") {
            findings.push(
                GateFinding::error(
                    "rustup-trust-rustc",
                    "Use canonical trustc from the selected Trust sysroot; rustup may only be selector convenience after proving that sysroot; rustup run trust rustc is not release evidence",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        for (legacy, canonical) in [
            ("rustdoc", "trustdoc"),
            ("rustfmt", "trustfmt"),
            ("cargo-fmt", "trustfmt"),
            ("clippy-driver", "tippy-driver"),
            ("cargo-clippy", "tippy"),
            ("rust-analyzer", "trust-analyzer"),
            ("miri", "trust-miri"),
            ("cargo-miri", "targo-miri"), // Trust: produced component is targo-miri
        ] {
            if has_rustup_trust_tool(line, legacy) {
                findings.push(
                    GateFinding::error(
                        format!("rustup-trust-{legacy}"),
                        format!(
                            "Use canonical {canonical} from the selected Trust sysroot; rustup may only be selector convenience after proving that sysroot; rustup run trust {legacy} is not release evidence"
                        ),
                    )
                    .with_location(path, line_number)
                    .with_text(trimmed),
                );
            }
        }

        if has_stage2_tool_path(line, "cargo") {
            findings.push(
                GateFinding::error(
                    "stage2-cargo-path",
                    "Stage2 Trust Cargo evidence should point at stage2/bin/targo, not stage2/bin/cargo",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        if has_stage2_tool_path(line, "rustc") {
            findings.push(
                GateFinding::error(
                    "stage2-rustc-path",
                    "Stage2 Trust compiler evidence should point at stage2/bin/trustc, not stage2/bin/rustc",
                )
                .with_location(path, line_number)
                .with_text(trimmed),
            );
        }

        for (legacy, canonical) in [
            ("rustdoc", "trustdoc"),
            ("rustfmt", "trustfmt"),
            ("cargo-fmt", "trustfmt"),
            ("clippy-driver", "tippy-driver"),
            ("cargo-clippy", "tippy"),
            ("rust-analyzer", "trust-analyzer"),
            ("miri", "trust-miri"),
            ("cargo-miri", "targo-miri"), // Trust: produced component is targo-miri
        ] {
            if has_stage2_tool_path(line, legacy) {
                findings.push(
                    GateFinding::error(
                        format!("stage2-{legacy}-path"),
                        format!(
                            "Stage2 Trust tool evidence should point at stage2/bin/{canonical}, not stage2/bin/{legacy}"
                        ),
                    )
                    .with_location(path, line_number)
                    .with_text(trimmed),
                );
            }
        }
    }

    GateReport::new("tool-names", findings)
}

/// Read files and check them with [`check_tool_names_text`].
pub fn check_tool_names_files<I, P>(paths: I) -> io::Result<GateReport>
where
    I: IntoIterator<Item = P>,
    P: AsRef<Path>,
{
    let mut findings = Vec::new();
    for path in paths {
        let path = path.as_ref();
        let text = fs::read_to_string(path)?;
        findings.extend(check_tool_names_text(path.display().to_string(), &text).findings);
    }

    Ok(GateReport::new("tool-names", findings))
}

/// Parsed owned-dependency row from `release/internal-repo-versions.toml`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct OwnedDependency {
    pub id: String,
    pub status: String,
    pub public_repo: String,
    pub version: String,
    pub public_tag: String,
    pub source_archive_url: String,
    pub source_sha256: String,
}

impl OwnedDependency {
    pub fn is_release_ready(&self) -> bool {
        self.release_blockers().is_empty()
    }

    fn release_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();

        if !self.status.eq_ignore_ascii_case("released") {
            blockers.push(format!("status must be 'released' (found {})", quoted(&self.status)));
        }

        if !is_public_repo_root(&self.public_repo) {
            blockers.push(format!(
                "public_repo must be under https://github.com/alabsystems/ (found {})",
                quoted(&self.public_repo)
            ));
        }

        if !is_semver_like(&self.version) {
            blockers.push(format!("version must be semver-like (found {})", quoted(&self.version)));
        }

        let expected_tag = format!("v{}", self.version.trim());
        if self.public_tag.trim() != expected_tag {
            blockers.push(format!(
                "public_tag must be {} (found {})",
                quoted(&expected_tag),
                quoted(&self.public_tag)
            ));
        }

        let expected_archive_url = format!(
            "{}/archive/refs/tags/{}.tar.gz",
            self.public_repo.trim_end_matches('/'),
            expected_tag
        );
        if self.source_archive_url.trim() != expected_archive_url {
            blockers.push(format!(
                "source_archive_url must be {} (found {})",
                quoted(&expected_archive_url),
                quoted(&self.source_archive_url)
            ));
        }

        if !is_lower_hex_sha256(&self.source_sha256) {
            blockers.push(format!(
                "source_sha256 must be 64 lowercase hex for the released source archive (found {})",
                quoted(&self.source_sha256)
            ));
        }

        blockers
    }

    fn display_id(&self) -> &str {
        if self.id.is_empty() { "<unnamed>" } else { self.id.as_str() }
    }
}

/// Parse the `[[repos]]` entries from an internal repo versions TOML string.
///
/// This is deliberately a narrow parser for the checked-in manifest shape:
/// string scalar keys inside `[[repos]]` tables are understood; arrays and
/// unrelated tables are ignored.
pub fn parse_internal_repo_versions_toml(toml: &str) -> Result<Vec<OwnedDependency>, ParseError> {
    let mut repos = Vec::new();
    let mut current: Option<OwnedDependency> = None;
    let mut in_repos = false;
    let mut in_array = false;

    for (line_index, raw_line) in toml.lines().enumerate() {
        let line_number = line_index + 1;
        let line_without_comment = strip_toml_comment(raw_line);
        let line = line_without_comment.trim();

        if line.is_empty() {
            continue;
        }

        if in_array {
            if line.contains(']') {
                in_array = false;
            }
            continue;
        }

        if line == "[[repos]]" {
            if let Some(repo) = current.take() {
                repos.push(repo);
            }
            current = Some(OwnedDependency::default());
            in_repos = true;
            continue;
        }

        if line.starts_with('[') {
            if let Some(repo) = current.take() {
                repos.push(repo);
            }
            in_repos = false;
            continue;
        }

        if !in_repos {
            continue;
        }

        let Some((key, value)) = line.split_once('=') else {
            return Err(ParseError::new(
                line_number,
                "expected key = value inside [[repos]] table",
            ));
        };

        let key = key.trim();
        let value = value.trim();
        if value.starts_with('[') {
            if !value.contains(']') {
                in_array = true;
            }
            continue;
        }

        if !matches!(
            key,
            "id" | "status"
                | "public_repo"
                | "version"
                | "public_tag"
                | "source_archive_url"
                | "source_sha256"
        ) {
            continue;
        }

        let Some(repo) = current.as_mut() else {
            continue;
        };
        let parsed = parse_toml_string(value).ok_or_else(|| {
            ParseError::new(line_number, format!("expected string value for repos.{key}"))
        })?;

        match key {
            "id" => repo.id = parsed,
            "status" => repo.status = parsed,
            "public_repo" => repo.public_repo = parsed,
            "version" => repo.version = parsed,
            "public_tag" => repo.public_tag = parsed,
            "source_archive_url" => repo.source_archive_url = parsed,
            "source_sha256" => repo.source_sha256 = parsed,
            _ => unreachable!("known repo keys are filtered before parsing"),
        }
    }

    if let Some(repo) = current {
        repos.push(repo);
    }

    Ok(repos)
}

/// Check owned internal dependency versions for the selected evidence profile.
pub fn check_owned_deps_toml(toml: &str, profile: EvidenceProfile) -> GateReport {
    let repos = match parse_internal_repo_versions_toml(toml) {
        Ok(repos) => repos,
        Err(err) => {
            return GateReport::new(
                "owned-deps",
                vec![GateFinding::error("owned-deps-parse", err.to_string())],
            );
        }
    };

    let mut findings = Vec::new();

    for repo in repos {
        let blockers = repo.release_blockers();
        if blockers.is_empty() {
            continue;
        }

        if !profile.reports_unreleased_owned_deps() {
            continue;
        }

        let message = format!(
            "owned dependency {} is not release-ready: {}",
            repo.display_id(),
            blockers.join("; ")
        );

        let code = "owned-dep-unreleased";
        if profile.blocks_unreleased_owned_deps() {
            findings.push(GateFinding::error(code, message));
        } else {
            findings.push(GateFinding::warning(code, message));
        }
    }

    GateReport::new("owned-deps", findings)
}

fn quoted(value: &str) -> String {
    let trimmed = value.trim();
    if trimmed.is_empty() { "<missing>".into() } else { format!("{trimmed:?}") }
}

fn is_public_repo_root(value: &str) -> bool {
    let trimmed = value.trim();
    let Some(repo) = trimmed.strip_prefix("https://github.com/alabsystems/") else {
        return false;
    };
    !repo.is_empty()
        && !repo.contains('/')
        && repo
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-'))
}

fn is_semver_like(value: &str) -> bool {
    let trimmed = value.trim();
    let core_end = trimmed.find(['-', '+']).unwrap_or(trimmed.len());
    let core = &trimmed[..core_end];
    let mut parts = core.split('.');
    let Some(major) = parts.next() else { return false };
    let Some(minor) = parts.next() else { return false };
    let Some(patch) = parts.next() else { return false };
    parts.next().is_none()
        && [major, minor, patch]
            .into_iter()
            .all(|part| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit()))
}

fn is_lower_hex_sha256(value: &str) -> bool {
    let trimmed = value.trim();
    trimmed.len() == 64
        && trimmed.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Version identity evidence required for release review.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct VersionIdentityEvidence {
    pub frontend: Option<String>,
    pub extension: Option<String>,
    pub compiler: Option<String>,
    pub documentation: Option<String>,
    pub formatter: Option<String>,
    pub cargo_formatter: Option<String>,
    pub tippy: Option<String>,
    pub targo_tippy: Option<String>,
    pub tippy_driver: Option<String>,
    pub analyzer: Option<String>,
    pub daemon: Option<String>,
    pub miri: Option<String>,
    pub targo_miri: Option<String>,
    pub candidate_commit: Option<String>,
}

impl VersionIdentityEvidence {
    #[allow(clippy::too_many_arguments)] // version-identity evidence records every component string at once
    pub fn new(
        frontend: impl Into<String>,
        extension: impl Into<String>,
        compiler: impl Into<String>,
        documentation: impl Into<String>,
        formatter: impl Into<String>,
        cargo_formatter: impl Into<String>,
        tippy: impl Into<String>,
        targo_tippy: impl Into<String>,
        tippy_driver: impl Into<String>,
        analyzer: impl Into<String>,
        daemon: impl Into<String>,
        candidate_commit: impl Into<String>,
    ) -> Self {
        Self {
            frontend: Some(frontend.into()),
            extension: Some(extension.into()),
            compiler: Some(compiler.into()),
            documentation: Some(documentation.into()),
            formatter: Some(formatter.into()),
            cargo_formatter: Some(cargo_formatter.into()),
            tippy: Some(tippy.into()),
            targo_tippy: Some(targo_tippy.into()),
            tippy_driver: Some(tippy_driver.into()),
            analyzer: Some(analyzer.into()),
            daemon: Some(daemon.into()),
            miri: None,
            targo_miri: None,
            candidate_commit: Some(candidate_commit.into()),
        }
    }
}

/// Validate required Trust command-surface and candidate-commit identity fields.
pub fn check_version_identity(evidence: &VersionIdentityEvidence) -> GateReport {
    let mut findings = Vec::new();

    require_non_empty_identity(&mut findings, "frontend", &evidence.frontend);
    require_non_empty_identity(&mut findings, "extension", &evidence.extension);
    require_non_empty_identity(&mut findings, "compiler", &evidence.compiler);
    require_non_empty_identity(&mut findings, "documentation", &evidence.documentation);
    require_non_empty_identity(&mut findings, "formatter", &evidence.formatter);
    require_non_empty_identity(&mut findings, "cargo-formatter", &evidence.cargo_formatter);
    require_non_empty_identity(&mut findings, "tippy", &evidence.tippy);
    require_non_empty_identity(&mut findings, "targo-tippy", &evidence.targo_tippy);
    require_non_empty_identity(&mut findings, "tippy-driver", &evidence.tippy_driver);
    require_non_empty_identity(&mut findings, "analyzer", &evidence.analyzer);
    require_non_empty_identity(&mut findings, "daemon", &evidence.daemon);
    reject_empty_optional_identity(&mut findings, "miri", &evidence.miri);
    reject_empty_optional_identity(&mut findings, "targo-miri", &evidence.targo_miri); // Trust: produced component is targo-miri

    match evidence.candidate_commit.as_deref().map(str::trim) {
        Some(commit) if is_plausible_git_commit(commit) => {}
        Some(_) => findings.push(GateFinding::error(
            "version-identity-candidate-commit",
            "candidate commit must be a 7 to 40 character hexadecimal Git id",
        )),
        None => findings.push(GateFinding::error(
            "version-identity-candidate-commit",
            "missing candidate commit identity",
        )),
    }

    GateReport::new("version-identity", findings)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    line: usize,
    message: String,
}

impl ParseError {
    fn new(line: usize, message: impl Into<String>) -> Self {
        Self { line, message: message.into() }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

impl std::error::Error for ParseError {}

fn require_non_empty_identity(
    findings: &mut Vec<GateFinding>,
    field: &'static str,
    value: &Option<String>,
) {
    if value.as_deref().map(str::trim).is_some_and(|v| !v.is_empty()) {
        return;
    }

    findings.push(GateFinding::error(
        format!("version-identity-{field}"),
        format!("missing {field} identity"),
    ));
}

fn is_plausible_git_commit(value: &str) -> bool {
    (7..=40).contains(&value.len()) && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn allowed_tool_context(line: &str) -> bool {
    contains_case_insensitive(line, "targo") // Trust: produced frontend is targo
        || contains_case_insensitive(line, "trustc")
        || contains_case_insensitive(line, "compiler/rustc")
        || contains_case_insensitive(line, "rustc-main")
        || contains_case_insensitive(line, "stage2-rustc")
        || contains_case_insensitive(line, "rustc-*-trust-src")
        || contains_case_insensitive(line, "rustc-src")
        || contains_case_insensitive(line, "rustc/trustc")
        || contains_case_insensitive(line, "trustc/rustc")
        || [
            "archive",
            "artifact",
            "ambient",
            "cache",
            "cargo-cache",
            "cargo-home",
            "CARGO_HOME",
            "Cargo.lock",
            "Cargo.toml",
            "cargo-clippy",
            "cargo-fmt",
            "cargo-miri",
            "targo-trust",
            "default-toolchain",
            "development override",
            "external",
            "forbidden",
            "host",
            "internal",
            "inherited",
            "lockfile",
            "nightly",
            "package",
            "registry",
            "real",
            "rust-lang",
            "rustup protocol",
            "stable",
            "stage0",
            "subcommand",
            "tarball",
            "upstream",
            "vanilla",
        ]
        .iter()
        .any(|word| contains_case_insensitive(line, word))
}

fn has_trust_targo_bin_as_cargo(line: &str) -> bool {
    if !contains_word(line, "TRUST_TARGO_BIN") {
        return false;
    }

    line.split(|ch: char| ch.is_whitespace() || matches!(ch, '"' | '\'' | '`' | ';'))
        .filter_map(|part| part.split_once('=').map(|(_, value)| value).or(Some(part)))
        .map(|part| {
            part.trim_matches(|ch: char| {
                !ch.is_ascii_alphanumeric() && ch != '/' && ch != '\\' && ch != '.'
            })
        })
        .any(|part| {
            let normalized = part.rsplit(['/', '\\']).next().unwrap_or(part);
            normalized == "cargo" || normalized == "cargo.exe"
        })
}

fn has_bare_tool_command(line: &str, tool: &str) -> bool {
    let lower = line.to_lowercase();
    lower.match_indices(tool).any(|(index, _)| {
        let before = lower[..index].chars().next_back();
        let after_index = index + tool.len();
        let after = lower[after_index..].chars().next();
        if !matches!(
            before,
            None | Some(' ' | '\t' | '\n' | '`' | '$' | ';' | '&' | '|' | '(' | '<')
        ) || !matches!(after, Some(ch) if ch.is_whitespace())
        {
            return false;
        }

        let next =
            lower[after_index..].split_whitespace().next().unwrap_or("").trim_start_matches('-');
        matches!(
            next,
            "build"
                | "check"
                | "clippy"
                | "doc"
                | "fetch"
                | "fmt"
                | "generate-lockfile"
                | "install"
                | "metadata"
                | "publish"
                | "run"
                | "test"
                | "trust"
                | "update"
                | "vendor"
                | "version"
                | "v"
                | "vv"
                | "print"
        )
    })
}

fn has_ambiguous_trust_tool_reference(line: &str, tool: &str) -> bool {
    if !contains_word_case_insensitive(line, tool)
        || has_trust_tool_phrase(line, tool)
        || has_rustup_trust_tool(line, tool)
        || has_stage2_tool_path(line, tool)
    {
        return false;
    }

    prose_words(line).iter().any(|word| {
        matches!(
            word.as_str(),
            "canonical"
                | "direct"
                | "public"
                | "stage2"
                | "stage3"
                | "trust"
                | "trust-owned"
                | "users"
                | "user"
        )
    })
}

fn has_trust_tool_phrase(line: &str, tool: &str) -> bool {
    let words = prose_words(line);
    words.windows(2).any(|pair| pair[0] == "trust" && pair[1] == tool)
        || words.windows(2).any(|pair| pair[0] == "trust-owned" && pair[1] == tool)
}

fn has_rustup_trust_tool(line: &str, tool: &str) -> bool {
    prose_words(line).windows(4).any(|pair| {
        pair[0] == "rustup" && pair[1] == "run" && pair[2] == "trust" && pair[3] == tool
    })
}

fn has_stage2_tool_path(line: &str, tool: &str) -> bool {
    line.split(|ch: char| ch.is_whitespace() || ch == '"' || ch == '\'').any(|part| {
        let part = part.trim_end_matches(|ch: char| !ch.is_ascii_alphanumeric());
        part.contains("stage2/bin/")
            && part.rsplit(['/', '\\']).next().is_some_and(|name| name == tool)
    })
}

fn contains_case_insensitive(haystack: &str, needle: &str) -> bool {
    haystack.to_lowercase().contains(&needle.to_lowercase())
}

fn contains_word(haystack: &str, needle: &str) -> bool {
    haystack
        .split(|ch: char| !(ch == '_' || ch == '-' || ch.is_ascii_alphanumeric()))
        .any(|word| word == needle)
}

fn contains_word_case_insensitive(haystack: &str, needle: &str) -> bool {
    haystack
        .split(|ch: char| !(ch == '_' || ch == '-' || ch.is_ascii_alphanumeric()))
        .any(|word| word.eq_ignore_ascii_case(needle))
}

fn prose_words(line: &str) -> Vec<String> {
    line.split(|ch: char| !(ch == '_' || ch == '-' || ch.is_ascii_alphanumeric()))
        .filter(|word| !word.is_empty())
        .map(str::to_lowercase)
        .collect()
}

fn strip_toml_comment(line: &str) -> &str {
    let mut in_string = false;
    let mut escaped = false;

    for (index, ch) in line.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }

        match ch {
            '\\' if in_string => escaped = true,
            '"' => in_string = !in_string,
            '#' if !in_string => return &line[..index],
            _ => {}
        }
    }

    line
}

fn parse_toml_string(value: &str) -> Option<String> {
    let value = value.trim();
    if !value.starts_with('"') {
        return None;
    }

    let mut parsed = String::new();
    let mut escaped = false;
    for ch in value[1..].chars() {
        if escaped {
            parsed.push(match ch {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                '"' => '"',
                '\\' => '\\',
                other => other,
            });
            escaped = false;
            continue;
        }

        match ch {
            '\\' => escaped = true,
            '"' => return Some(parsed),
            other => parsed.push(other),
        }
    }

    None
}

fn reject_empty_optional_identity(
    findings: &mut Vec<GateFinding>,
    field: &'static str,
    value: &Option<String>,
) {
    if value.as_deref().is_some_and(|value| value.trim().is_empty()) {
        findings.push(GateFinding::error(
            format!("version-identity-{field}"),
            format!("{field} identity must be non-empty when supplied"),
        ));
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;

    #[test]
    fn tool_names_accepts_canonical_tools_and_internal_context() {
        let report = check_tool_names_text(
            "release.log",
            "\
build/aarch64-unknown-linux-gnu/stage2/bin/targo --version
build/aarch64-unknown-linux-gnu/stage2/bin/trustc -Vv
rustup run trust targo --version paired with selected Trust sysroot proof
internal upstream cargo/rustc bootstrap artifacts are not public release evidence
",
        );

        assert_eq!(report.status, GateStatus::Pass);
        assert!(report.findings.is_empty());
    }

    #[test]
    fn tool_names_rejects_trust_aliases_even_with_compatibility_context() {
        let report = check_tool_names_text(
            "release.log",
            "\
compatibility aliases: cargo/rustc
rustup run trust cargo build
rustup run trust rustc -Vv
rustup run trust rustfmt --version
rustup run trust cargo-clippy --version
rustup run trust rust-analyzer --version
stage2/bin/cargo compatibility alias beside stage2/bin/targo
stage2/bin/rustc compatibility alias beside stage2/bin/trustc
stage2/bin/rustfmt compatibility alias beside stage2/bin/trustfmt
stage2/bin/cargo-clippy compatibility alias beside stage2/bin/tippy
stage2/bin/rust-analyzer compatibility alias beside stage2/bin/trust-analyzer
",
        );

        assert_eq!(report.status, GateStatus::Fail);
        let codes: Vec<_> = report.findings.iter().map(|finding| finding.code.as_str()).collect();
        assert!(codes.contains(&"rustup-trust-cargo"), "{codes:?}");
        assert!(codes.contains(&"rustup-trust-rustc"), "{codes:?}");
        assert!(codes.contains(&"rustup-trust-rustfmt"), "{codes:?}");
        assert!(codes.contains(&"rustup-trust-cargo-clippy"), "{codes:?}");
        assert!(codes.contains(&"rustup-trust-rust-analyzer"), "{codes:?}");
        assert!(codes.contains(&"stage2-cargo-path"), "{codes:?}");
        assert!(codes.contains(&"stage2-rustc-path"), "{codes:?}");
        assert!(codes.contains(&"stage2-rustfmt-path"), "{codes:?}");
        assert!(codes.contains(&"stage2-cargo-clippy-path"), "{codes:?}");
        assert!(codes.contains(&"stage2-rust-analyzer-path"), "{codes:?}");
    }

    #[test]
    fn tool_names_default_paths_include_docs_native_tests_and_e2e_scripts() {
        let root = temp_dir_path("tool-name-paths");
        fs::create_dir_all(root.join("docs")).unwrap();
        fs::create_dir_all(root.join("targo-trust/tests")).unwrap();
        fs::create_dir_all(root.join("tests")).unwrap();
        fs::write(root.join("docs/trust-naming.md"), "").unwrap();
        fs::write(root.join("targo-trust/tests/release_cli.rs"), "").unwrap();
        fs::write(root.join("tests/e2e_basic_contracts_smoke.sh"), "").unwrap();

        let paths = default_tool_name_evidence_paths(&root);

        assert!(paths.contains(&root.join("docs/trust-naming.md")));
        assert!(paths.contains(&root.join("targo-trust/tests/release_cli.rs")));
        assert!(paths.contains(&root.join("tests/e2e_basic_contracts_smoke.sh")));

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn tool_names_rejects_ambiguous_cargo_and_rustc_evidence() {
        let report = check_tool_names_text(
            "release.log",
            "\
Trust Cargo produced the release evidence
rustup run trust cargo build
build/aarch64-apple-darwin/stage2/bin/cargo --version
Trust rustc compiled it
rustup run trust rustc -Vv
build/aarch64-apple-darwin/stage2/bin/rustc -Vv
TRUST_CARGO_BIN=/tmp/cargo
TRUST_RUSTC_BIN=/tmp/rustc
TRUST_TARGO_BIN=/tmp/stage2/bin/cargo
cargo test --all
rustc --version --verbose
Public users run targo trust through the Trust toolchain
",
        );

        assert_eq!(report.status, GateStatus::Fail);
        let codes: Vec<_> = report.findings.iter().map(|finding| finding.code.as_str()).collect();
        assert!(codes.contains(&"trust-cargo-phrase"), "{codes:?}");
        assert!(codes.contains(&"rustup-trust-cargo"), "{codes:?}");
        assert!(codes.contains(&"stage2-cargo-path"), "{codes:?}");
        assert!(codes.contains(&"trust-rustc-phrase"), "{codes:?}");
        assert!(codes.contains(&"rustup-trust-rustc"), "{codes:?}");
        assert!(codes.contains(&"stage2-rustc-path"), "{codes:?}");
        assert!(codes.contains(&"trust-cargo-env"), "{codes:?}");
        assert!(codes.contains(&"trust-rustc-env"), "{codes:?}");
        assert!(codes.contains(&"trust-targo-bin-cargo"), "{codes:?}");
        assert!(codes.contains(&"bare-cargo-command"), "{codes:?}");
        assert!(codes.contains(&"bare-rustc-command"), "{codes:?}");
    }

    #[test]
    fn tool_names_reads_file_inputs() {
        let path = temp_file_path("tool-names");
        fs::write(&path, "Trust Cargo built release evidence\n").unwrap();

        let report = check_tool_names_files([path.as_path()]).unwrap();

        assert_eq!(report.status, GateStatus::Fail);
        assert_eq!(report.findings[0].location.as_ref().unwrap().line, 1);

        let _ = fs::remove_file(path);
    }

    #[test]
    fn owned_deps_public_profile_rejects_planned_entries() {
        let report = check_owned_deps_toml(
            r#"
schema_version = "trust.internal_repo_versions.v1"

[[repos]]
id = "ay"
status = "planned"
public_repo = "https://github.com/alabsystems/ay"
version = "0.9.0"
public_tag = "v0.9.0"
source_archive_url = "https://github.com/alabsystems/ay/archive/refs/tags/v0.9.0.tar.gz"
source_sha256 = ""
"#,
            EvidenceProfile::Public,
        );

        assert_eq!(report.status, GateStatus::Fail);
        assert_eq!(report.findings[0].severity, FindingSeverity::Error);
        assert!(report.findings[0].message.contains("ay"));
    }

    #[test]
    fn owned_deps_metadata_profile_warns_for_planned_entries() {
        let report = check_owned_deps_toml(
            r#"
[[repos]]
id = "trust-mc"
status = "planned"
public_tag = "v0.67.0"
source_sha256 = ""
"#,
            EvidenceProfile::Metadata,
        );

        assert_eq!(report.status, GateStatus::Warn);
        assert_eq!(report.exit_code_kind(), ExitCodeKind::WarningsOnly);
        assert_eq!(report.findings[0].severity, FindingSeverity::Warning);
    }

    #[test]
    fn owned_deps_local_profile_accepts_private_most_recent_entries() {
        let report = check_owned_deps_toml(
            r#"
[[repos]]
id = "trust-mc"
status = "planned"
public_tag = "v0.67.0"
source_sha256 = ""
"#,
            EvidenceProfile::Local,
        );

        assert_eq!(report.status, GateStatus::Pass);
        assert!(report.findings.is_empty());
    }

    #[test]
    fn owned_deps_accepts_released_entries_with_checksum() {
        let report = check_owned_deps_toml(
            r#"
[[repos]]
id = "trust-wp"
status = "released"
public_repo = "https://github.com/alabsystems/trust-wp"
version = "0.1.0"
public_tag = "v0.1.0"
source_archive_url = "https://github.com/alabsystems/trust-wp/archive/refs/tags/v0.1.0.tar.gz"
source_sha256 = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
workspace_dependency_paths = [
  "first-party/trust-wp/crates/trust-wp-core",
]
"#,
            EvidenceProfile::Release,
        );

        assert_eq!(report.status, GateStatus::Pass);
    }

    #[test]
    fn owned_deps_release_readiness_names_archive_and_checksum_blockers() {
        // Fixture deliberately uses a non-canonical owner so the
        // `public_repo must be under https://github.com/alabsystems/` blocker fires
        // alongside the public_tag / archive URL / sha256 blockers.
        let report = check_owned_deps_toml(
            r#"
[[repos]]
id = "trust-vc"
status = "released"
public_repo = "https://github.com/some-fork/trust-vc"
version = "1.0.0"
public_tag = "v1.0.1"
source_archive_url = "https://github.com/some-fork/trust-vc/archive/refs/tags/v1.0.1.tar.gz"
source_sha256 = "abc123"
"#,
            EvidenceProfile::Release,
        );

        assert_eq!(report.status, GateStatus::Fail);
        let message = &report.findings[0].message;
        assert!(
            message.contains("public_repo must be under https://github.com/alabsystems/"),
            "missing public_repo blocker in: {message}"
        );
        assert!(
            message.contains("public_tag must be \"v1.0.0\""),
            "missing public_tag blocker in: {message}"
        );
        assert!(
            message.contains("source_archive_url must be"),
            "missing source_archive_url blocker in: {message}"
        );
        assert!(
            message.contains("source_sha256 must be 64 lowercase hex"),
            "missing source_sha256 blocker in: {message}"
        );
    }

    #[test]
    fn owned_deps_reports_parse_errors() {
        let report = check_owned_deps_toml(
            r#"
[[repos]]
id = ay
"#,
            EvidenceProfile::Release,
        );

        assert_eq!(report.status, GateStatus::Fail);
        assert_eq!(report.findings[0].code, "owned-deps-parse");
    }

    #[test]
    fn version_identity_requires_all_identity_fields() {
        let report = check_version_identity(&VersionIdentityEvidence {
            frontend: Some("targo 0.1.0".to_string()),
            extension: None,
            compiler: Some("trustc 1.96.0-trust".to_string()),
            documentation: None,
            formatter: Some("trustfmt 1.96.0-trust".to_string()),
            cargo_formatter: None,
            tippy: Some("tippy 1.96.0-trust".to_string()),
            targo_tippy: None,
            tippy_driver: None,
            analyzer: Some("trust-analyzer 1.96.0-trust".to_string()),
            daemon: None,
            miri: Some("".to_string()),
            targo_miri: None,
            candidate_commit: Some("not-a-commit".to_string()),
        });

        assert_eq!(report.status, GateStatus::Fail);
        let codes: Vec<_> = report.findings.iter().map(|finding| finding.code.as_str()).collect();
        assert!(codes.contains(&"version-identity-extension"));
        assert!(codes.contains(&"version-identity-documentation"));
        assert!(codes.contains(&"version-identity-cargo-formatter"));
        assert!(codes.contains(&"version-identity-targo-tippy"));
        assert!(codes.contains(&"version-identity-tippy-driver"));
        assert!(codes.contains(&"version-identity-daemon"));
        assert!(codes.contains(&"version-identity-miri"));
        assert!(codes.contains(&"version-identity-candidate-commit"));
    }

    #[test]
    fn version_identity_accepts_complete_identity() {
        let report = check_version_identity(&VersionIdentityEvidence::new(
            "targo 0.1.0",
            "targo-trust 0.1.0",
            "trustc 1.96.0-trust",
            "trustdoc 1.96.0-trust",
            "trustfmt 1.96.0-trust",
            "targo-fmt 1.96.0-trust",
            "tippy 1.96.0-trust",
            "tippy 1.96.0-trust",
            "tippy-driver 1.96.0-trust",
            "trust-analyzer 1.96.0-trust",
            "trustd 1.96.0-trust",
            "abcdef1234567890",
        ));

        assert_eq!(report.status, GateStatus::Pass);
    }

    #[test]
    fn aggregate_report_prefers_fail_over_warn() {
        let aggregate = AggregateReport::new(vec![
            GateReport::new("warn", vec![GateFinding::warning("w", "warning")]),
            GateReport::new("fail", vec![GateFinding::error("e", "error")]),
        ]);

        assert_eq!(aggregate.status(), GateStatus::Fail);
        assert_eq!(aggregate.exit_code_kind(), ExitCodeKind::ReleaseBlocked);
    }

    fn temp_file_path(prefix: &str) -> PathBuf {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        std::env::temp_dir().join(format!("{prefix}-{nonce}.txt"))
    }

    fn temp_dir_path(prefix: &str) -> PathBuf {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        std::env::temp_dir().join(format!("{prefix}-{nonce}"))
    }
}
