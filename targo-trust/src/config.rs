// targo-trust configuration: the `[trust]` table of the project manifest.
//
// Trust policy is a property of the project, not of the invocation
// (DESIGN_PHILOSOPHY.md §3), so it belongs in the manifest the project already
// has rather than in a second file the toolchain has to go looking for. The
// stand-alone `trust.toml` remains readable for one release so existing
// checkouts keep verifying while they migrate.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use serde::{Deserialize, Deserializer, de};

use crate::input_limits::{MAX_RELEASE_METADATA_BYTES, read_bounded_utf8_file};
use crate::intent::contained_manifest_relative_path;

pub(crate) const DEFAULT_CODEGEN_BACKEND: &str = "llvm";
pub(crate) const DEFAULT_TRUST_PROFILE: &str = "unix_hardened";

/// The manifest file names targo discovers, native spelling first. Kept in the
/// same order as targo's own `find_root_manifest_for_wd` so the file that
/// carries the build definition is the file that carries the Trust policy.
pub(crate) const MANIFEST_NAMES: [&str; 2] = ["Targo.toml", "Cargo.toml"];

/// The manifest table that carries Trust policy.
pub(crate) const TRUST_TABLE: &str = "trust";

/// The retired stand-alone configuration file.
pub(crate) const LEGACY_CONFIG_FILE: &str = "trust.toml";

pub(crate) fn normalize_verification_level(name: &str) -> Option<&'static str> {
    match name.trim().to_ascii_uppercase().as_str() {
        "L0" => Some("L0"),
        "L1" => Some("L1"),
        "L2" => Some("L2"),
        _ => None,
    }
}

pub(crate) fn known_verification_levels() -> &'static [&'static str] {
    &["L0", "L1", "L2"]
}

pub(crate) fn normalize_codegen_backend(name: &str) -> Option<&'static str> {
    match name.trim().to_ascii_lowercase().as_str() {
        "llvm" => Some("llvm"),
        "trust-cg" => Some("trust-cg"),
        _ => None,
    }
}

pub(crate) fn known_codegen_backend_names() -> &'static [&'static str] {
    &["llvm", "trust-cg"]
}

/// How much proof evidence a dependency must carry before this project will
/// build against it.
///
/// The default is [`DepEvidencePolicy::None`], and that is a considered
/// position rather than an unfinished one. Every crate on crates.io today was
/// published by a toolchain that does not emit a proof certificate, so a
/// stricter default would not harden anything — it would refuse the entire
/// ecosystem on the first `targo build`, which is a capability loss dressed up
/// as a safety improvement. A project that has brought its dependency tree up
/// to a standard can say so; nobody else is billed for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum DepEvidencePolicy {
    /// Dependencies are not asked for evidence. Missing certificates are not
    /// findings, and `targo tree --proof` still shows what is there.
    #[default]
    None,
    /// Every dependency must ship a `.trust/proof.cert`. Presence only: the
    /// certificate is parsed and its identity checked against the package, but
    /// its verdict distribution is reported rather than gated. This is the
    /// honest middle rung — it proves a dependency was built by a Trust
    /// toolchain, not that it was proved.
    Present,
    /// Every dependency must ship a certificate whose own verdict is a clean
    /// verified run: no failed rows, no unknown rows, no assumption rows.
    Verified,
}

impl DepEvidencePolicy {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Present => "present",
            Self::Verified => "verified",
        }
    }
}

pub(crate) fn normalize_dep_evidence(name: &str) -> Option<DepEvidencePolicy> {
    match name.trim().to_ascii_lowercase().as_str() {
        "none" => Some(DepEvidencePolicy::None),
        "present" => Some(DepEvidencePolicy::Present),
        "verified" => Some(DepEvidencePolicy::Verified),
        _ => None,
    }
}

pub(crate) fn known_dep_evidence_names() -> &'static [&'static str] {
    &["none", "present", "verified"]
}

/// Every key the `[trust]` table accepts. `TrustConfigFile` is
/// `deny_unknown_fields`, so this list is also the complete set of spellings a
/// project may write; a typo fails the load instead of being ignored.
pub(crate) fn known_config_keys() -> &'static [&'static str] {
    &[
        "enabled",
        "level",
        "timeout_ms",
        "function_budget_ms",
        "skip_functions",
        "codegen_backend",
        "hardened",
        "trust_profile",
        "intent",
        "require_dep_evidence",
    ]
}

/// The wire form of a `[trust]` table.
///
/// Every key is optional because "the project wrote this" and "the project
/// accepted our default" have to stay distinguishable: workspace-wide policy
/// may only fill keys a member left unwritten, never overwrite one the member
/// spelled out. Resolving defaults happens after that merge, in
/// [`ResolvedTrustConfig::into_config`].
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct TrustConfigFile {
    #[serde(default)]
    pub(crate) enabled: Option<bool>,
    #[serde(default, deserialize_with = "deserialize_level")]
    pub(crate) level: Option<String>,
    #[serde(default, deserialize_with = "deserialize_positive_timeout")]
    pub(crate) timeout_ms: Option<u64>,
    #[serde(default, deserialize_with = "deserialize_positive_function_budget_ms")]
    pub(crate) function_budget_ms: Option<u64>,
    #[serde(default)]
    pub(crate) skip_functions: Option<Vec<String>>,
    #[serde(default)]
    pub(crate) codegen_backend: Option<String>,
    #[serde(default)]
    pub(crate) hardened: Option<bool>,
    #[serde(default)]
    pub(crate) trust_profile: Option<String>,
    #[serde(default)]
    pub(crate) intent: Option<String>,
    #[serde(default)]
    pub(crate) require_dep_evidence: Option<String>,
}

impl TrustConfigFile {
    /// Fill keys this table left unwritten from a workspace-wide table.
    ///
    /// This is the member-beats-workspace precedence gate. It is soundness
    /// relevant in one direction: a workspace default must never displace a
    /// member's own declaration, because that would let a permissive workspace
    /// root quietly lower a member crate's verification level. Filling only
    /// unwritten keys makes that impossible by construction.
    fn fill_unset_from(&mut self, workspace: &TrustConfigFile) {
        let TrustConfigFile {
            enabled,
            level,
            timeout_ms,
            function_budget_ms,
            skip_functions,
            codegen_backend,
            hardened,
            trust_profile,
            intent,
            require_dep_evidence,
        } = workspace;
        self.enabled = self.enabled.or(*enabled);
        self.level = self.level.take().or_else(|| level.clone());
        self.timeout_ms = self.timeout_ms.or(*timeout_ms);
        self.function_budget_ms = self.function_budget_ms.or(*function_budget_ms);
        self.skip_functions = self.skip_functions.take().or_else(|| skip_functions.clone());
        self.codegen_backend = self.codegen_backend.take().or_else(|| codegen_backend.clone());
        self.hardened = self.hardened.or(*hardened);
        self.trust_profile = self.trust_profile.take().or_else(|| trust_profile.clone());
        self.require_dep_evidence =
            self.require_dep_evidence.take().or_else(|| require_dep_evidence.clone());
        // `intent` deliberately does not inherit: it names a document beneath
        // the declaring manifest's own directory, so a workspace-root value
        // would resolve against the wrong directory for every member.
        let _ = intent;
    }
}

/// An intent document named by configuration, already checked for containment
/// beneath the directory of the file that named it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConfiguredIntent {
    /// Path to the document.
    pub(crate) path: PathBuf,
    /// The manifest or config file that named it.
    pub(crate) declared_in: PathBuf,
}

/// Where the effective policy came from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TrustConfigSource {
    /// A `[trust]` table in the named manifest.
    Manifest(PathBuf),
    /// The deprecated stand-alone `trust.toml`.
    LegacyFile(PathBuf),
    /// Nothing was declared.
    Defaults,
}

impl TrustConfigSource {
    pub(crate) fn describe(&self) -> String {
        match self {
            TrustConfigSource::Manifest(path) => {
                format!("[{TRUST_TABLE}] in {}", path.display())
            }
            TrustConfigSource::LegacyFile(path) => path.display().to_string(),
            TrustConfigSource::Defaults => "defaults".to_string(),
        }
    }

    pub(crate) fn is_legacy(&self) -> bool {
        matches!(self, TrustConfigSource::LegacyFile(_))
    }
}

/// Effective configuration.
#[derive(Debug, Clone)]
pub(crate) struct TrustConfig {
    pub(crate) enabled: bool,
    pub(crate) level: String,
    pub(crate) timeout_ms: u64,
    pub(crate) function_budget_ms: u64,
    pub(crate) skip_functions: Vec<String>,
    pub(crate) codegen_backend: Option<String>,
    pub(crate) hardened: Option<bool>,
    pub(crate) trust_profile: Option<String>,
    pub(crate) intent: Option<ConfiguredIntent>,
    pub(crate) require_dep_evidence: DepEvidencePolicy,
}

/// Effective configuration plus the provenance a report needs to name it.
#[derive(Debug, Clone)]
pub(crate) struct ResolvedTrustConfig {
    pub(crate) config: TrustConfig,
    pub(crate) source: TrustConfigSource,
    /// The workspace-root manifest that supplied defaults, when one did.
    pub(crate) workspace_defaults_from: Option<PathBuf>,
}

#[derive(Debug, Clone)]
pub(crate) struct TrustConfigLoadError {
    pub(crate) path: PathBuf,
    pub(crate) action: &'static str,
    pub(crate) detail: String,
}

impl std::fmt::Display for TrustConfigLoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "failed to {} {}: {}", self.action, self.path.display(), self.detail)
    }
}

pub(crate) fn default_level() -> String {
    // Trust: batteries-on default. The verification front door
    // (`targo trust check/build/report`) proves at the maximal L2 (domain)
    // level by default — L0 safety + L1 functional + L2 domain obligations —
    // so the toolchain attempts every proof it can without an opt-in flag
    // (DESIGN_PHILOSOPHY.md §2 "All batteries on by default"). A repo can still
    // dial down via `[trust] level = "L0"|"L1"` for triage.
    "L2".to_string()
}
pub(crate) fn default_timeout() -> u64 {
    5000
}

pub(crate) fn default_function_budget_ms() -> u64 {
    120_000
}

fn deserialize_level<'de, D>(deserializer: D) -> Result<Option<String>, D::Error>
where
    D: Deserializer<'de>,
{
    let raw = String::deserialize(deserializer)?;
    normalize_verification_level(&raw).map(|level| Some(level.to_string())).ok_or_else(|| {
        let known = known_verification_levels().join(", ");
        de::Error::custom(format!("invalid verification level `{raw}` (expected one of: {known})"))
    })
}

fn deserialize_positive_timeout<'de, D>(deserializer: D) -> Result<Option<u64>, D::Error>
where
    D: Deserializer<'de>,
{
    let timeout_ms = u64::deserialize(deserializer)?;
    if timeout_ms == 0 {
        return Err(de::Error::custom("timeout_ms must be greater than zero"));
    }
    Ok(Some(timeout_ms))
}

fn deserialize_positive_function_budget_ms<'de, D>(
    deserializer: D,
) -> Result<Option<u64>, D::Error>
where
    D: Deserializer<'de>,
{
    let function_budget_ms = u64::deserialize(deserializer)?;
    if function_budget_ms == 0 {
        return Err(de::Error::custom("function_budget_ms must be greater than zero"));
    }
    Ok(Some(function_budget_ms))
}

impl Default for TrustConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            level: default_level(),
            timeout_ms: default_timeout(),
            function_budget_ms: default_function_budget_ms(),
            skip_functions: vec![],
            codegen_backend: None,
            hardened: None,
            trust_profile: None,
            intent: None,
            require_dep_evidence: DepEvidencePolicy::default(),
        }
    }
}

impl TrustConfig {
    /// Load configuration for verifier entrypoints.
    ///
    /// A project with no declaration still means defaults, but a declaration
    /// that is present must be readable and valid. `targo trust
    /// check/report/build` are fail-closed proof commands, so they must not
    /// silently fall back to defaults when the repository supplied an invalid
    /// policy.
    pub(crate) fn load_for_verification(
        dir: &Path,
        manifest_path: Option<&Path>,
    ) -> Result<Self, TrustConfigLoadError> {
        let resolved = resolve_trust_config(dir, manifest_path)?;
        if resolved.source.is_legacy() {
            eprintln!("targo trust: warning: {}", legacy_config_deprecation_notice());
        }
        if !matches!(resolved.source, TrustConfigSource::Defaults) {
            eprintln!("targo trust: loaded config from {}", resolved.source.describe());
        }
        if let Some(workspace) = &resolved.workspace_defaults_from {
            eprintln!(
                "targo trust: unset keys inherited from [{TRUST_TABLE}] in {}",
                workspace.display()
            );
        }
        Ok(resolved.config)
    }
}

/// The one sentence that tells a project where its policy now lives. Both the
/// verifier front door and `targo trust doctor` print it, so the replacement is
/// never described two different ways.
pub(crate) fn legacy_config_deprecation_notice() -> String {
    format!(
        "`{LEGACY_CONFIG_FILE}` is deprecated and is read for one more release; \
         move its keys into the `[{TRUST_TABLE}]` table of `{}` (or `{}`)",
        MANIFEST_NAMES[0], MANIFEST_NAMES[1]
    )
}

/// Resolve the effective policy for a project rooted at `dir`.
///
/// `manifest_path`, when the caller already knows which manifest it is building,
/// pins the file the `[trust]` table is read from; otherwise the native
/// `Targo.toml` is preferred over the compatibility `Cargo.toml`, matching
/// targo's own manifest discovery.
pub(crate) fn resolve_trust_config(
    dir: &Path,
    manifest_path: Option<&Path>,
) -> Result<ResolvedTrustConfig, TrustConfigLoadError> {
    let manifest = match manifest_path {
        Some(path) if path.is_file() => Some(path.to_path_buf()),
        _ => discover_manifest(dir),
    };

    let declared_in_manifest = match &manifest {
        Some(path) => read_trust_table(path)?.map(|file| (path.clone(), file)),
        None => None,
    };
    let legacy_path = dir.join(LEGACY_CONFIG_FILE);
    let declared_in_legacy_file =
        read_config_file(&legacy_path)?.map(|file| (legacy_path.clone(), file));

    let (source, mut file) = match (declared_in_manifest, declared_in_legacy_file) {
        (Some((manifest_path, _)), Some((legacy_path, _))) => {
            // Two live policy surfaces cannot both be authoritative, and a
            // proof command must not pick one by accident.
            return Err(TrustConfigLoadError {
                path: legacy_path,
                action: "validate",
                detail: format!(
                    "Trust policy is declared twice: in [{TRUST_TABLE}] of {} and in this file; \
                     delete the deprecated file so one policy governs the project",
                    manifest_path.display()
                ),
            });
        }
        (Some((path, file)), None) => (TrustConfigSource::Manifest(path), file),
        (None, Some((path, file))) => (TrustConfigSource::LegacyFile(path), file),
        (None, None) => (TrustConfigSource::Defaults, TrustConfigFile::default()),
    };

    let workspace = workspace_trust_table(dir, manifest.as_deref())?;
    let workspace_defaults_from = match &workspace {
        Some((path, table)) => {
            file.fill_unset_from(table);
            Some(path.clone())
        }
        None => None,
    };

    let declaring_file = match &source {
        TrustConfigSource::Manifest(path) | TrustConfigSource::LegacyFile(path) => Some(path),
        TrustConfigSource::Defaults => None,
    };
    let config = into_config(file, dir, declaring_file)?;
    Ok(ResolvedTrustConfig { config, source, workspace_defaults_from })
}

/// Apply defaults and validate the values that only make sense once the merge
/// is complete.
fn into_config(
    file: TrustConfigFile,
    dir: &Path,
    declaring_file: Option<&PathBuf>,
) -> Result<TrustConfig, TrustConfigLoadError> {
    let codegen_backend = match file.codegen_backend {
        Some(raw) => match normalize_codegen_backend(&raw) {
            Some(normalized) => Some(normalized.to_string()),
            None => {
                let known = known_codegen_backend_names().join(", ");
                return Err(TrustConfigLoadError {
                    path: declaring_file.cloned().unwrap_or_else(|| dir.to_path_buf()),
                    action: "validate",
                    detail: format!("unknown codegen backend `{raw}` (expected one of: {known})"),
                });
            }
        },
        None => None,
    };

    let intent = match (file.intent, declaring_file) {
        (Some(raw), Some(declared_in)) => {
            let relative = contained_manifest_relative_path(dir, raw.trim()).map_err(|detail| {
                TrustConfigLoadError {
                    path: declared_in.clone(),
                    action: "validate",
                    detail: format!("[{TRUST_TABLE}] intent: {detail}"),
                }
            })?;
            relative.map(|relative| ConfiguredIntent {
                path: dir.join(relative),
                declared_in: declared_in.clone(),
            })
        }
        _ => None,
    };

    let require_dep_evidence = match file.require_dep_evidence {
        Some(raw) => match normalize_dep_evidence(&raw) {
            Some(policy) => policy,
            None => {
                let known = known_dep_evidence_names().join(", ");
                return Err(TrustConfigLoadError {
                    path: declaring_file.cloned().unwrap_or_else(|| dir.to_path_buf()),
                    action: "validate",
                    detail: format!(
                        "unknown dependency evidence policy `{raw}` (expected one of: {known})"
                    ),
                });
            }
        },
        None => DepEvidencePolicy::default(),
    };

    Ok(TrustConfig {
        enabled: file.enabled.unwrap_or(true),
        level: file.level.unwrap_or_else(default_level),
        timeout_ms: file.timeout_ms.unwrap_or_else(default_timeout),
        function_budget_ms: file.function_budget_ms.unwrap_or_else(default_function_budget_ms),
        skip_functions: file.skip_functions.unwrap_or_default(),
        codegen_backend,
        hardened: file.hardened,
        trust_profile: file.trust_profile,
        intent,
        require_dep_evidence,
    })
}

/// The manifest that governs `dir`, native spelling preferred.
pub(crate) fn discover_manifest(dir: &Path) -> Option<PathBuf> {
    MANIFEST_NAMES.iter().map(|name| dir.join(name)).find(|path| path.is_file())
}

/// Read `[trust]` out of a manifest. Absent table means "nothing declared";
/// a present but malformed table is an error, never a silent default.
pub(crate) fn read_trust_table(
    manifest_path: &Path,
) -> Result<Option<TrustConfigFile>, TrustConfigLoadError> {
    let Some(content) = read_config_source(manifest_path)? else {
        return Ok(None);
    };
    let document = content.parse::<toml::Value>().map_err(|error| TrustConfigLoadError {
        path: manifest_path.to_path_buf(),
        action: "parse",
        detail: error.to_string(),
    })?;
    let Some(table) = document.get(TRUST_TABLE) else {
        return Ok(None);
    };
    TrustConfigFile::deserialize(table.clone())
        .map(Some)
        .map_err(|error| unknown_key_error(manifest_path, error.to_string()))
}

/// Read a whole file as a `[trust]`-shaped table. Used only by the deprecated
/// stand-alone config file, whose entire body is the table.
fn read_config_file(path: &Path) -> Result<Option<TrustConfigFile>, TrustConfigLoadError> {
    let Some(content) = read_config_source(path)? else {
        return Ok(None);
    };
    toml::from_str::<TrustConfigFile>(&content)
        .map(Some)
        .map_err(|error| unknown_key_error(path, error.to_string()))
}

/// A key nobody recognises is a typo the project meant to have an effect. Say
/// so, and say which spellings exist, rather than verifying under a policy the
/// author did not write.
fn unknown_key_error(path: &Path, detail: String) -> TrustConfigLoadError {
    let action = if detail.contains("unknown field") { "validate" } else { "parse" };
    let detail = if action == "validate" {
        format!("[{TRUST_TABLE}]: {detail} (supported keys: {})", known_config_keys().join(", "))
    } else {
        detail
    };
    TrustConfigLoadError { path: path.to_path_buf(), action, detail }
}

/// Read a configuration source, distinguishing "absent" from "unreadable".
/// The bounded read also rejects anything that is not an exact regular file,
/// so a symlink cannot redirect policy discovery.
fn read_config_source(path: &Path) -> Result<Option<String>, TrustConfigLoadError> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => {
            return Err(TrustConfigLoadError {
                path: path.to_path_buf(),
                action: "inspect",
                detail: error.to_string(),
            });
        }
    }
    read_bounded_utf8_file(path, MAX_RELEASE_METADATA_BYTES)
        .map(Some)
        .map_err(|error| TrustConfigLoadError {
            path: path.to_path_buf(),
            action: "read",
            detail: error.to_string(),
        })
}

/// The nearest ancestor manifest that declares a `[workspace]`, together with
/// its `[trust]` table. Only ancestors are considered: when `dir` is itself the
/// workspace root its own table is already the member table.
///
/// An ancestor manifest that cannot be read or parsed is passed over rather
/// than failed on. Those files govern nothing here unless they turn out to be
/// the workspace root, and cargo rejects a broken workspace root on its own;
/// failing on every unrelated ancestor would turn any stray file above the
/// project into a verification outage. Passing one over can only fall back to
/// the built-in defaults, which are the strict end of every key.
fn workspace_trust_table(
    dir: &Path,
    member_manifest: Option<&Path>,
) -> Result<Option<(PathBuf, TrustConfigFile)>, TrustConfigLoadError> {
    for ancestor in dir.ancestors().skip(1) {
        for name in MANIFEST_NAMES {
            let candidate = ancestor.join(name);
            if Some(candidate.as_path()) == member_manifest || !candidate.is_file() {
                continue;
            }
            let Ok(Some(content)) = read_config_source(&candidate) else {
                continue;
            };
            let Ok(document) = content.parse::<toml::Value>() else {
                continue;
            };
            if document.get("workspace").is_none() {
                continue;
            }
            let table = match document.get(TRUST_TABLE) {
                Some(table) => TrustConfigFile::deserialize(table.clone())
                    .map_err(|error| unknown_key_error(&candidate, error.to_string()))?,
                None => return Ok(None),
            };
            return Ok(Some((candidate, table)));
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write(path: &Path, contents: &str) {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("create fixture dir");
        }
        std::fs::write(path, contents).expect("write fixture");
    }

    #[test]
    fn manifest_trust_table_is_the_canonical_surface() {
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n\n[trust]\nlevel = \"L1\"\ntimeout_ms = 9000\n",
        );

        let resolved = resolve_trust_config(root.path(), None).expect("load");
        assert_eq!(resolved.config.level, "L1");
        assert_eq!(resolved.config.timeout_ms, 9000);
        assert_eq!(resolved.config.function_budget_ms, default_function_budget_ms());
        assert_eq!(resolved.source, TrustConfigSource::Manifest(root.path().join("Cargo.toml")));
    }

    #[test]
    fn native_manifest_wins_over_the_compatibility_manifest() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("Cargo.toml"), "[package]\nname=\"d\"\n\n[trust]\nlevel=\"L0\"\n");
        write(&root.path().join("Targo.toml"), "[package]\nname=\"d\"\n\n[trust]\nlevel=\"L1\"\n");

        let resolved = resolve_trust_config(root.path(), None).expect("load");
        assert_eq!(resolved.config.level, "L1");
        assert_eq!(resolved.source, TrustConfigSource::Manifest(root.path().join("Targo.toml")));
    }

    #[test]
    fn a_manifest_without_the_table_means_defaults() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("Cargo.toml"), "[package]\nname = \"demo\"\n");

        let resolved = resolve_trust_config(root.path(), None).expect("load");
        assert_eq!(resolved.source, TrustConfigSource::Defaults);
        assert_eq!(resolved.config.level, default_level());
    }

    #[test]
    fn the_deprecated_file_still_configures_a_project() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("Cargo.toml"), "[package]\nname = \"demo\"\n");
        write(&root.path().join("trust.toml"), "level = \"L1\"\nhardened = false\n");

        let resolved = resolve_trust_config(root.path(), None).expect("load");
        assert_eq!(resolved.config.level, "L1");
        assert_eq!(resolved.config.hardened, Some(false));
        assert!(resolved.source.is_legacy());
        assert!(legacy_config_deprecation_notice().contains("[trust]"));
        assert!(legacy_config_deprecation_notice().contains("Targo.toml"));
    }

    #[test]
    fn declaring_policy_on_both_surfaces_is_an_error() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("Cargo.toml"), "[package]\nname=\"d\"\n\n[trust]\nlevel=\"L1\"\n");
        write(&root.path().join("trust.toml"), "level = \"L0\"\n");

        let error = resolve_trust_config(root.path(), None)
            .expect_err("two live policy surfaces must not resolve");
        assert_eq!(error.action, "validate");
        assert!(error.detail.contains("declared twice"), "{error}");
    }

    #[test]
    fn an_unknown_key_names_the_supported_spellings() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("Cargo.toml"), "[package]\nname=\"d\"\n\n[trust]\nlevl = \"L1\"\n");

        let error = resolve_trust_config(root.path(), None).expect_err("a typo must fail the load");
        assert_eq!(error.action, "validate");
        assert!(error.detail.contains("unknown field"), "{error}");
        assert!(error.detail.contains("function_budget_ms"), "{error}");
    }

    #[test]
    fn an_unknown_key_in_the_deprecated_file_is_equally_an_error() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("trust.toml"), "levl = \"L1\"\n");

        let error = resolve_trust_config(root.path(), None).expect_err("a typo must fail the load");
        assert_eq!(error.action, "validate");
        assert!(error.detail.contains("unknown field"), "{error}");
    }

    #[test]
    fn a_member_level_survives_a_weaker_workspace_default() {
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[workspace]\nmembers = [\"member\"]\n\n[trust]\nlevel = \"L0\"\ntimeout_ms = 1000\n",
        );
        let member = root.path().join("member");
        write(
            &member.join("Cargo.toml"),
            "[package]\nname = \"member\"\n\n[trust]\nlevel = \"L1\"\n",
        );

        let resolved = resolve_trust_config(&member, None).expect("load");
        assert_eq!(resolved.config.level, "L1", "a workspace default must not weaken a member");
        assert_eq!(resolved.config.timeout_ms, 1000, "unwritten keys still inherit");
        assert_eq!(resolved.workspace_defaults_from, Some(root.path().join("Cargo.toml")));
    }

    #[test]
    fn a_member_without_a_table_inherits_the_workspace_default() {
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[workspace]\nmembers = [\"member\"]\n\n[trust]\nlevel = \"L1\"\n",
        );
        let member = root.path().join("member");
        write(&member.join("Cargo.toml"), "[package]\nname = \"member\"\n");

        let resolved = resolve_trust_config(&member, None).expect("load");
        assert_eq!(resolved.config.level, "L1");
    }

    #[test]
    fn a_workspace_root_reads_its_own_table_once() {
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[workspace]\nmembers = []\n\n[trust]\nlevel = \"L0\"\n",
        );

        let resolved = resolve_trust_config(root.path(), None).expect("load");
        assert_eq!(resolved.config.level, "L0");
        assert_eq!(resolved.workspace_defaults_from, None);
    }

    #[test]
    fn a_non_workspace_ancestor_does_not_supply_defaults() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("Cargo.toml"), "[package]\nname=\"outer\"\n\n[trust]\nlevel=\"L0\"\n");
        let inner = root.path().join("inner");
        write(&inner.join("Cargo.toml"), "[package]\nname = \"inner\"\n");

        let resolved = resolve_trust_config(&inner, None).expect("load");
        assert_eq!(resolved.config.level, default_level());
        assert_eq!(resolved.workspace_defaults_from, None);
    }

    #[test]
    fn intent_resolves_against_the_manifest_that_named_it() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("docs/intent.md"), "design says saturate");
        write(
            &root.path().join("Cargo.toml"),
            "[package]\nname=\"d\"\n\n[trust]\nintent = \"docs/intent.md\"\n",
        );

        let resolved = resolve_trust_config(root.path(), None).expect("load");
        let intent = resolved.config.intent.expect("configured intent");
        assert_eq!(intent.path, root.path().join("docs/intent.md"));
        assert_eq!(intent.declared_in, root.path().join("Cargo.toml"));
    }

    #[test]
    fn intent_may_not_escape_the_project() {
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[package]\nname=\"d\"\n\n[trust]\nintent = \"../outside.md\"\n",
        );

        let error = resolve_trust_config(root.path(), None).expect_err("escape must fail closed");
        assert_eq!(error.action, "validate");
        assert!(error.detail.contains("contained relative path"), "{error}");
    }

    #[test]
    fn an_invalid_level_is_rejected_with_the_known_levels() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("Cargo.toml"), "[package]\nname=\"d\"\n\n[trust]\nlevel = \"L9\"\n");

        let error = resolve_trust_config(root.path(), None).expect_err("bad level must fail");
        assert!(error.detail.contains("invalid verification level"), "{error}");
    }

    #[test]
    fn a_zero_budget_is_rejected() {
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[package]\nname=\"d\"\n\n[trust]\nfunction_budget_ms = 0\n",
        );

        let error = resolve_trust_config(root.path(), None).expect_err("zero budget must fail");
        assert!(error.detail.contains("greater than zero"), "{error}");
    }

    #[test]
    fn an_unknown_codegen_backend_is_rejected() {
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[package]\nname=\"d\"\n\n[trust]\ncodegen_backend = \"cranelift\"\n",
        );

        let error = resolve_trust_config(root.path(), None).expect_err("bad backend must fail");
        assert_eq!(error.action, "validate");
        assert!(error.detail.contains("unknown codegen backend"), "{error}");
    }

    #[test]
    fn an_explicit_manifest_path_pins_the_surface() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("Cargo.toml"), "[package]\nname=\"d\"\n\n[trust]\nlevel=\"L0\"\n");
        write(&root.path().join("Targo.toml"), "[package]\nname=\"d\"\n\n[trust]\nlevel=\"L1\"\n");

        let resolved =
            resolve_trust_config(root.path(), Some(&root.path().join("Cargo.toml"))).expect("load");
        assert_eq!(resolved.config.level, "L0");
    }

    #[test]
    fn verification_config_rejects_oversized_input_before_toml_parsing() {
        let root = tempfile::tempdir().expect("config fixture");
        let path = root.path().join("trust.toml");
        let file = std::fs::File::create(&path).expect("create oversized config");
        file.set_len(MAX_RELEASE_METADATA_BYTES as u64 + 1).expect("size oversized config");

        let error = resolve_trust_config(root.path(), None)
            .expect_err("oversized config must fail closed");
        assert_eq!(error.action, "read");
        assert!(error.detail.contains("safety limit"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn verification_config_rejects_a_leaf_symlink() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("config fixture");
        let target = root.path().join("policy.toml");
        std::fs::write(&target, "level = \"L2\"\n").expect("write target config");
        symlink(&target, root.path().join("trust.toml")).expect("link config");

        let error = resolve_trust_config(root.path(), None)
            .expect_err("symlinked config must fail closed");
        assert_eq!(error.action, "read");
        assert!(error.detail.contains("not a regular file"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn a_symlinked_manifest_cannot_smuggle_in_policy() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("config fixture");
        let target = root.path().join("elsewhere.toml");
        std::fs::write(&target, "[package]\nname=\"d\"\n\n[trust]\nlevel=\"L0\"\n")
            .expect("write target manifest");
        symlink(&target, root.path().join("Cargo.toml")).expect("link manifest");

        let error = resolve_trust_config(root.path(), None)
            .expect_err("symlinked manifest must fail closed");
        assert_eq!(error.action, "read");
    }
}
