// targo-trust configuration: the `[trust]` table of the project manifest.
//
// Trust policy is a property of the project, not of the invocation
// (DESIGN_PHILOSOPHY.md §3), so it belongs in the manifest the project already
// has rather than in a second file the toolchain has to go looking for. The
// stand-alone `trust.toml` remains readable for one release so existing
// checkouts keep verifying while they migrate.
//
// One workspace, one policy (plan §3.6; T7c): the workspace root's table
// governs every member, whichever member a run starts in or selects, and a
// member's own `[trust]` table (or `trust.toml`) is refused, naming its keys
// and the root to move them to. targo's `Workspace` refuses a member's table
// and a `trust.toml` beside a member on every command that loads the
// workspace, whichever package it selects; this loader refuses the table and
// the file of the member a run starts in (doctor, standalone and proof-cert
// read the policy without a sibling targo).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};

use serde::{Deserialize, Deserializer, de};

use crate::input_limits::{MAX_RELEASE_METADATA_BYTES, read_bounded_utf8_file};
use crate::intent::contained_manifest_relative_path;
use crate::project_root::lexically_normalized;

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
        "effort",
        "backstop",
        "skip_functions",
        "codegen_backend",
        "hardened",
        "trust_profile",
        "intent",
        "require_dep_evidence",
    ]
}

/// `[trust]` keys this toolchain no longer reads, each with the setting that
/// replaced it. A table that still names one is refused with that replacement
/// rather than as an unknown key, so a project learns where its setting went
/// instead of only that it is wrong.
///
/// `compiler_timeout_secs` was the absolute wall-clock ceiling on one verified
/// compiler process (default 28,800 s), a second backstop beside `backstop`.
/// T7 folds it into `backstop` (plan §3.2, §3.6; DECISION_QUEUE "T7b"): the
/// one per-mille multiplier now scales that ceiling with every other clock, so
/// a run has one backstop, and its firing is COULD NOT RUN (exit 3).
pub(crate) const RETIRED_CONFIG_KEYS: &[(&str, &str)] = &[(
    "compiler_timeout_secs",
    "retired on 2026-10-11: `[trust] backstop` in the workspace root's table is the one \
     wall-clock backstop, and it scales the compiler-process ceiling (8 hours at the builtin \
     1000 per mille) with the per-query and per-function clocks. Delete this key, and raise \
     `backstop` in the workspace root's [trust] table if a run needs a longer ceiling",
)];

/// The wire form of a `[trust]` table.
///
/// Every key is optional because "the project wrote this" and "the project
/// accepted our default" stay distinguishable (a level the table declares is
/// recorded as declared). Defaults are applied in `into_config`.
#[derive(Debug, Clone, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct TrustConfigFile {
    #[serde(default)]
    pub(crate) enabled: Option<bool>,
    #[serde(default, deserialize_with = "deserialize_level")]
    pub(crate) level: Option<String>,
    /// The one solver-effort count's scale `k`, SAT conflicts per distinct
    /// query term ([`trust_types::determinism::EffortScale`]; plan §3.2a).
    #[serde(default, deserialize_with = "deserialize_effort")]
    pub(crate) effort: Option<trust_types::determinism::EffortScale>,
    /// The wall-clock backstop, per mille of the reference clocks
    /// ([`trust_types::determinism::Backstop`]; plan §3.6): the per-query and
    /// per-function clocks targo passes the compiler, and the bounds targo
    /// holds each verified compiler process to.
    #[serde(default, deserialize_with = "deserialize_backstop")]
    pub(crate) backstop: Option<trust_types::determinism::Backstop>,
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
    /// Distinguishes a manifest assertion from the implicit L2 default.
    pub(crate) level_declared: bool,
    /// Checked Cargo requirements, resolved before lane/session construction.
    pub(crate) project_policy: Option<crate::pipeline::project_policy::ProjectTrustPolicy>,
    /// The one solver-effort count's scale `k` (`-Ztrust-verify-effort`), the
    /// workspace root's `[trust] effort`.
    pub(crate) effort: trust_types::determinism::EffortScale,
    /// The wall-clock backstop (`[trust] backstop`), from which targo derives
    /// `-Ztrust-verify-timeout-ms`, `-Ztrust-verify-function-budget-ms` and
    /// the bounds of each verified compiler process
    /// (`pipeline::run::CompilerProcessBounds::from_backstop`).
    pub(crate) backstop: trust_types::determinism::Backstop,
    /// `--worker-threads`: the verifier worker-thread cap this run passes the
    /// compiler (`-Ztrust-verify-worker-threads`); 0, the default, passes
    /// nothing and caps nothing. A per-run scheduling choice from the command
    /// line, never a manifest key (DECISION_QUEUE T7a): the budget profile
    /// records it, and it is not in the profile id (plan §3.6).
    pub(crate) worker_threads: u64,
    /// `--no-proc-macro-isolation` clears this. Set, the default, the sibling
    /// Targo passes `-Ztrust-proc-macro-isolation` to every unit whose
    /// proc-macro TCB is in scope on a host with the worker sandbox (D21).
    /// Cleared, the lane carries `-Ztrust-proc-macro-isolation=no` and a
    /// verified unit with an unaudited proc-macro dependency is refused as it
    /// was before the worker existed. A per-run choice from the command line,
    /// never a manifest key, and one that can only refuse more.
    pub(crate) proc_macro_isolation: bool,
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
    /// The manifest of the workspace member the run started in, when it is
    /// one: its policy is then its workspace root's (`source`).
    pub(crate) member_manifest: Option<PathBuf>,
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

fn deserialize_effort<'de, D>(
    deserializer: D,
) -> Result<Option<trust_types::determinism::EffortScale>, D::Error>
where
    D: Deserializer<'de>,
{
    let k = u64::deserialize(deserializer)?;
    trust_types::determinism::EffortScale::parse(&k.to_string())
        .map(Some)
        .map_err(|error| de::Error::custom(format!("effort: {error}")))
}

fn deserialize_backstop<'de, D>(
    deserializer: D,
) -> Result<Option<trust_types::determinism::Backstop>, D::Error>
where
    D: Deserializer<'de>,
{
    let per_mille = u64::deserialize(deserializer)?;
    trust_types::determinism::Backstop::parse(&per_mille.to_string())
        .map(Some)
        .map_err(|error| de::Error::custom(format!("backstop: {error}")))
}

impl Default for TrustConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            level: default_level(),
            level_declared: false,
            project_policy: None,
            effort: trust_types::determinism::EffortScale::BUILTIN,
            backstop: trust_types::determinism::Backstop::BUILTIN,
            worker_threads: 0,
            proc_macro_isolation: true,
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
        if let Some(member) = &resolved.member_manifest {
            eprintln!(
                "targo trust: {} is a workspace member; its policy is the workspace root's ({})",
                member.display(),
                resolved.source.describe()
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
///
/// A workspace member's policy is its workspace root's, read as the root reads
/// its own; a member that declares a `[trust]` table or a `trust.toml` of its
/// own is refused, naming its keys and the root's manifest (plan §3.6).
pub(crate) fn resolve_trust_config(
    dir: &Path,
    manifest_path: Option<&Path>,
) -> Result<ResolvedTrustConfig, TrustConfigLoadError> {
    let manifest = match manifest_path {
        Some(path) if path.is_file() => Some(path.to_path_buf()),
        _ => discover_manifest(dir),
    };
    // The workspace root's table is policy for every member, so the root is
    // the one targo builds against: Cargo's own search, never "the nearest
    // ancestor that declares [workspace]".
    let root = match manifest.as_deref() {
        Some(member) => member_workspace_root(member, cargo_home().as_deref())?,
        None => None,
    };
    let Some(root) = root else {
        return resolve_own_trust_config(dir, manifest);
    };
    let member = manifest.expect("a workspace root was found for a manifest");
    refuse_member_policy(&member, &dir.join(LEGACY_CONFIG_FILE), &root)?;
    let root_dir = root.parent().map(Path::to_path_buf).unwrap_or_default();
    let resolved = resolve_own_trust_config(&root_dir, Some(root))?;
    Ok(ResolvedTrustConfig { member_manifest: Some(member), ..resolved })
}

/// Refuse a workspace member's own policy: a `[trust]` table in its manifest
/// or a deprecated `trust.toml` beside it. One run uses one policy, the
/// workspace root's, whichever member it starts in or selects, so a member
/// table could only be ignored (a policy its author believes is in force) or
/// be obeyed in some runs and not others. The refusal names the keys as they
/// are written, before they are read as policy.
fn refuse_member_policy(
    member: &Path,
    legacy_file: &Path,
    root: &Path,
) -> Result<(), TrustConfigLoadError> {
    let refusal = |path: &Path, what: String| TrustConfigLoadError {
        path: path.to_path_buf(),
        action: "validate",
        detail: format!(
            "{what}, but [{TRUST_TABLE}] is workspace policy: one workspace has one policy, the \
             workspace root's, whichever member a run starts in or selects. Move it to \
             [{TRUST_TABLE}] in {} (the workspace root), or make this package a workspace of \
             its own",
            root.display()
        ),
    };
    let named = |table: Option<&toml::Value>| -> String {
        let keys: Vec<String> = table
            .and_then(toml::Value::as_table)
            .map(|entries| entries.keys().map(|key| format!("`{key}`")).collect())
            .unwrap_or_default();
        if keys.is_empty() { "no keys".to_string() } else { keys.join(", ") }
    };
    if let Some(document) = read_manifest_document(member)? {
        if let Some(table) = document.get(TRUST_TABLE) {
            return Err(refusal(
                member,
                format!(
                    "this workspace member declares a [{TRUST_TABLE}] table ({})",
                    named(Some(table))
                ),
            ));
        }
    }
    if let Some(content) = read_config_source(legacy_file)? {
        let table = content.parse::<toml::Value>().ok();
        return Err(refusal(
            legacy_file,
            format!(
                "this workspace member has a deprecated `{LEGACY_CONFIG_FILE}` ({})",
                named(table.as_ref())
            ),
        ));
    }
    Ok(())
}

/// The policy of a project that is its own workspace root, or of no
/// workspace: its manifest's `[trust]` table or its deprecated `trust.toml`.
fn resolve_own_trust_config(
    dir: &Path,
    manifest: Option<PathBuf>,
) -> Result<ResolvedTrustConfig, TrustConfigLoadError> {
    let declared_in_manifest = match &manifest {
        Some(path) => read_trust_table(path)?.map(|file| (path.clone(), file)),
        None => None,
    };
    let legacy_path = dir.join(LEGACY_CONFIG_FILE);
    let declared_in_legacy_file =
        read_config_file(&legacy_path)?.map(|file| (legacy_path.clone(), file));

    let (source, file) = match (declared_in_manifest, declared_in_legacy_file) {
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

    // The deprecated file sets no budget. The workspace root's [trust] table is
    // the one spelling of `effort` and `backstop` (plan §3.6; DECISION_QUEUE
    // BUDGET-1), and the file, read for one more release for the keys it has
    // always carried, is not a second one.
    if let TrustConfigSource::LegacyFile(legacy) = &source {
        if file.effort.is_some() || file.backstop.is_some() {
            let root = manifest
                .as_ref()
                .map_or_else(|| "Cargo.toml".to_string(), |root| root.display().to_string());
            return Err(TrustConfigLoadError {
                path: legacy.clone(),
                action: "validate",
                detail: format!(
                    "the deprecated `{LEGACY_CONFIG_FILE}` cannot set effort or backstop: a budget \
                     is set only in the workspace root's [{TRUST_TABLE}] table; move them to \
                     [{TRUST_TABLE}] in {root}"
                ),
            });
        }
    }

    let declaring_file = match &source {
        TrustConfigSource::Manifest(path) | TrustConfigSource::LegacyFile(path) => Some(path),
        TrustConfigSource::Defaults => None,
    };
    let config = into_config(file, dir, declaring_file)?;
    Ok(ResolvedTrustConfig { config, source, member_manifest: None })
}

/// Apply defaults and validate the values that only make sense once the whole
/// table is read.
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

    // A profile label selects the obligation set, and nothing else in the
    // toolchain reads it. `-Ztrust-verify-profile` has exactly one consumer in
    // the compiler, so a label the registry does not know generates the
    // obligations of no profile at all — while `apply_configured_trust_profile`
    // still turns hardened mode ON for it, `targo trust` still prints
    // "hardened profile `<name>` enabled", and `report.rs` still copies that
    // banner into `hardened.profile.name` in the proof record. A typo was
    // therefore a silent downgrade that the evidence actively denied.
    //
    // REFUSED, not repaired to the nearest registered profile: a fallback
    // would verify something other than what this project committed, and would
    // record a profile name the project never wrote — the same surprise in the
    // opposite direction. A committed label naming a profile that does not
    // exist is a configuration error, so it fails the load exactly like an
    // unknown `codegen_backend` or an invalid `level`, and exactly like the
    // typo'd KEY that `deny_unknown_fields` already refuses. Turning hardened
    // obligations off remains `hardened = false`: a typed boolean, resolved
    // before any label is consulted, that no misspelling can produce by
    // accident.
    let trust_profile = match file.trust_profile {
        // Stored in the registry's spelling, like `codegen_backend` above: the
        // banner, the `-Ztrust-verify-profile` value and the proof record then
        // all name the profile the way the registry names it.
        Some(raw) => match trust_vcgen::canonical_profile(&raw) {
            Some(canonical) => Some(canonical.to_string()),
            None => {
                let known = trust_vcgen::known_hardened_profiles().join(", ");
                return Err(TrustConfigLoadError {
                    path: declaring_file.cloned().unwrap_or_else(|| dir.to_path_buf()),
                    action: "validate",
                    detail: format!(
                        "unknown trust profile `{raw}` (expected one of: {known}); \
                         a profile label selects the hardened obligation set, so an unregistered \
                         one would verify strictly less than this table asks for — write \
                         `hardened = false` to turn hardened obligations off deliberately"
                    ),
                });
            }
        },
        None => None,
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
        level_declared: file.level.is_some(),
        project_policy: None,
        level: file.level.unwrap_or_else(default_level),
        effort: file.effort.unwrap_or(trust_types::determinism::EffortScale::BUILTIN),
        backstop: file.backstop.unwrap_or(trust_types::determinism::Backstop::BUILTIN),
        worker_threads: 0,
        proc_macro_isolation: true,
        skip_functions: file.skip_functions.unwrap_or_default(),
        codegen_backend,
        hardened: file.hardened,
        trust_profile,
        intent,
        require_dep_evidence,
    })
}

/// The manifest whose `[trust]` table is the policy of the project at `dir`:
/// its workspace root's when the project is a workspace member (one workspace,
/// one policy), else its own. `None` when `dir` has no manifest.
pub(crate) fn policy_manifest(dir: &Path) -> Result<Option<PathBuf>, TrustConfigLoadError> {
    let Some(manifest) = discover_manifest(dir) else {
        return Ok(None);
    };
    Ok(Some(member_workspace_root(&manifest, cargo_home().as_deref())?.unwrap_or(manifest)))
}

/// The directory of the workspace root that governs `dir`: the nearest
/// manifest at or above `dir` (native spelling first), then that package's
/// workspace root by Cargo's own search ([`policy_manifest`]). It is the
/// directory whose `target/` Cargo uses when no target directory is
/// configured. `None` when no manifest is at or above `dir`.
pub(crate) fn workspace_root_dir(dir: &Path) -> Result<Option<PathBuf>, TrustConfigLoadError> {
    let Some(manifest) = dir.ancestors().find_map(discover_manifest) else {
        return Ok(None);
    };
    let package_dir = manifest.parent().unwrap_or(dir);
    let root_manifest = policy_manifest(package_dir)?.unwrap_or(manifest.clone());
    Ok(Some(root_manifest.parent().unwrap_or(package_dir).to_path_buf()))
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
    trust_table_policy(manifest_path, table).map(Some)
}

/// Read a whole file as a `[trust]`-shaped table. Used only by the deprecated
/// stand-alone config file, whose entire body is the table.
fn read_config_file(path: &Path) -> Result<Option<TrustConfigFile>, TrustConfigLoadError> {
    let Some(content) = read_config_source(path)? else {
        return Ok(None);
    };
    let table = content.parse::<toml::Value>().map_err(|error| TrustConfigLoadError {
        path: path.to_path_buf(),
        action: "parse",
        detail: error.to_string(),
    })?;
    trust_table_policy(path, &table).map(Some)
}

/// Read one `[trust]`-shaped table, declared in `path`, as policy. A retired
/// key is refused with the setting that replaced it ([`RETIRED_CONFIG_KEYS`]);
/// any other key the table does not accept is refused by name.
fn trust_table_policy(
    path: &Path,
    table: &toml::Value,
) -> Result<TrustConfigFile, TrustConfigLoadError> {
    let retired = table
        .as_table()
        .and_then(|entries| RETIRED_CONFIG_KEYS.iter().find(|(key, _)| entries.contains_key(*key)));
    if let Some((key, replacement)) = retired {
        return Err(TrustConfigLoadError {
            path: path.to_path_buf(),
            action: "validate",
            detail: format!("[{TRUST_TABLE}] `{key}` was {replacement}"),
        });
    }
    TrustConfigFile::deserialize(table.clone())
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
    read_bounded_utf8_file(path, MAX_RELEASE_METADATA_BYTES).map(Some).map_err(|error| {
        TrustConfigLoadError { path: path.to_path_buf(), action: "read", detail: error.to_string() }
    })
}

/// Read and parse one manifest of the workspace-root search. An absent file is
/// `None`; one that cannot be read or parsed is an error, as it is to Cargo.
fn read_manifest_document(path: &Path) -> Result<Option<toml::Value>, TrustConfigLoadError> {
    let Some(content) = read_config_source(path)? else {
        return Ok(None);
    };
    content.parse::<toml::Value>().map(Some).map_err(|error| TrustConfigLoadError {
        path: path.to_path_buf(),
        action: "parse",
        detail: error.to_string(),
    })
}

/// What Cargo's workspace-root search reads from one manifest
/// (`to_workspace_config` in the fork's `util/toml/mod.rs`): a `[workspace]`
/// table, with the `members` and `exclude` lists that decide whom it governs,
/// or a member, with or without a `package.workspace` pointer to its root.
#[derive(Debug)]
enum WorkspaceRole {
    Root { root_dir: PathBuf, members: Option<Vec<String>>, exclude: Vec<String> },
    Member { pointer: Option<String> },
}

/// The manifest keys a [`WorkspaceRole`] is read from. Every other key is left
/// alone here; Cargo reads, and refuses, the rest on its own.
#[derive(Deserialize)]
struct WorkspaceKeys {
    #[serde(default)]
    workspace: Option<WorkspaceTableKeys>,
    #[serde(default)]
    package: Option<PackageWorkspaceKey>,
    /// Cargo's legacy spelling of `[package]`.
    #[serde(default)]
    project: Option<PackageWorkspaceKey>,
}

#[derive(Deserialize)]
struct WorkspaceTableKeys {
    #[serde(default)]
    members: Option<Vec<String>>,
    #[serde(default)]
    exclude: Option<Vec<String>>,
}

#[derive(Deserialize)]
struct PackageWorkspaceKey {
    #[serde(default)]
    workspace: Option<String>,
}

impl WorkspaceRole {
    fn read(path: &Path, document: &toml::Value) -> Result<Self, TrustConfigLoadError> {
        let keys =
            WorkspaceKeys::deserialize(document.clone()).map_err(|error| TrustConfigLoadError {
                path: path.to_path_buf(),
                action: "parse",
                detail: error.to_string(),
            })?;
        let pointer = keys.package.or(keys.project).and_then(|package| package.workspace);
        match (keys.workspace, pointer) {
            (Some(workspace), None) => Ok(WorkspaceRole::Root {
                root_dir: path.parent().map(Path::to_path_buf).unwrap_or_default(),
                members: workspace.members,
                exclude: workspace.exclude.unwrap_or_default(),
            }),
            (None, pointer) => Ok(WorkspaceRole::Member { pointer }),
            (Some(_), Some(_)) => Err(TrustConfigLoadError {
                path: path.to_path_buf(),
                action: "validate",
                detail: "cannot configure both `package.workspace` and `[workspace]`, only one \
                         can be specified"
                    .to_string(),
            }),
        }
    }

    /// Cargo's `WorkspaceConfig::get_ws_root`: the root manifest that this
    /// manifest, at `self_path`, names for the package at `look_from`.
    fn root_for(&self, self_path: &Path, look_from: &Path) -> Option<PathBuf> {
        match self {
            WorkspaceRole::Root { .. } if self.excludes(look_from) => None,
            WorkspaceRole::Root { .. } => Some(self_path.to_path_buf()),
            // `read_root_pointer`: the named directory's `Cargo.toml`, always.
            WorkspaceRole::Member { pointer: Some(pointer) } => Some(lexically_normalized(
                &self_path.parent().unwrap_or(Path::new("")).join(pointer).join("Cargo.toml"),
            )),
            WorkspaceRole::Member { pointer: None } => None,
        }
    }

    /// Cargo's `WorkspaceRootConfig::is_excluded`: beneath an `exclude` entry
    /// and beneath no `members` entry, each compared as a path prefix as it is
    /// written (a glob is not expanded).
    fn excludes(&self, manifest: &Path) -> bool {
        let WorkspaceRole::Root { root_dir, members, exclude } = self else {
            return false;
        };
        let beneath = |entry: &String| manifest.starts_with(root_dir.join(entry));
        exclude.iter().any(beneath) && !members.iter().flatten().any(beneath)
    }
}

/// Cargo's home as the `targo` this run starts resolves it
/// (`home::cargo_home_with_cwd`): `CARGO_HOME`, against the working directory
/// when it is relative, else `.cargo` in the user's home directory.
pub(crate) fn cargo_home() -> Option<PathBuf> {
    match std::env::var_os("CARGO_HOME").filter(|home| !home.is_empty()) {
        Some(home) => {
            let home = PathBuf::from(home);
            if home.is_absolute() {
                Some(home)
            } else {
                std::env::current_dir().ok().map(|cwd| cwd.join(home))
            }
        }
        None => std::env::home_dir().map(|home| home.join(".cargo")),
    }
}

/// The manifest targo takes as the workspace root of the package whose
/// manifest is `member_manifest` (`member` is what that manifest declares).
/// `None` means the package is its own root.
///
/// This is Cargo's search, `Workspace::find_root` and `find_root_iter` in the
/// fork's `core/workspace.rs`, over the keys it reads:
/// - the package's own `[workspace]` makes it the root, unless that table
///   excludes the package itself;
/// - its `package.workspace` names the root;
/// - otherwise the `Cargo.toml` of each ancestor directory is asked in turn,
///   nearest first and starting above the package's own directory. The first
///   that names a root for the package names it: a `[workspace]` that does not
///   exclude the package, or a member's pointer. A `[workspace]` that excludes
///   it is passed by, so a workspace further out may still be its root. The
///   walk stops at a `target/package` directory and after `cargo_home`, and
///   reads `Cargo.toml` only: targo's ancestor search has no `Targo.toml`.
///
/// A manifest on that walk that cannot be read or parsed is an error, as it is
/// to Cargo ("failed searching for potential workspace"), and so is a
/// symlinked one, which could otherwise redirect the search. Whether the
/// package really is a member of the root found is not judged here: Cargo
/// refuses a package that believes it is in a workspace when it is not, before
/// anything compiles.
fn cargo_workspace_root(
    member_manifest: &Path,
    member: &WorkspaceRole,
    cargo_home: Option<&Path>,
) -> Result<Option<PathBuf>, TrustConfigLoadError> {
    if let Some(root) = member.root_for(member_manifest, member_manifest) {
        return Ok(Some(root));
    }
    let mut last: Option<&Path> = None;
    for dir in member_manifest.ancestors().skip(2) {
        if dir.ends_with("target/package") || (last.is_some() && last == cargo_home) {
            break;
        }
        last = Some(dir);
        let candidate = dir.join("Cargo.toml");
        if !candidate.exists() {
            continue;
        }
        let searching = |mut error: TrustConfigLoadError| {
            error.detail = format!(
                "{}; it is on the workspace-root search of {}, so the workspace that governs \
                 that package cannot be determined",
                error.detail,
                member_manifest.display()
            );
            error
        };
        let Some(document) = read_manifest_document(&candidate).map_err(searching)? else {
            continue;
        };
        let role = WorkspaceRole::read(&candidate, &document).map_err(searching)?;
        if let Some(root) = role.root_for(&candidate, member_manifest) {
            return Ok(Some(root));
        }
    }
    Ok(None)
}

/// The workspace root targo builds the package at `member_manifest` against,
/// when that is another manifest. `None` when the package is its own root (or
/// in no workspace): its own table is then the root table.
///
/// The root is [`cargo_workspace_root`]'s, so a `[workspace]` that excludes the
/// package, or that the package's `package.workspace` does not name, governs
/// nothing here, and a `[trust]` table outside the workspace being built is
/// never read. The root found must declare `[workspace]`; a pointer to
/// anything else is refused, as Cargo refuses it.
fn member_workspace_root(
    member_manifest: &Path,
    cargo_home: Option<&Path>,
) -> Result<Option<PathBuf>, TrustConfigLoadError> {
    // Cargo's `root_manifest`: against the working directory, then normalized.
    let member_manifest = match std::env::current_dir() {
        Ok(cwd) if member_manifest.is_relative() => {
            lexically_normalized(&cwd.join(member_manifest))
        }
        _ => lexically_normalized(member_manifest),
    };
    let Some(member_document) = read_manifest_document(&member_manifest)? else {
        return Ok(None);
    };
    let member = WorkspaceRole::read(&member_manifest, &member_document)?;
    let Some(root) = cargo_workspace_root(&member_manifest, &member, cargo_home)? else {
        return Ok(None);
    };
    let document = if root == member_manifest {
        member_document
    } else {
        let Some(document) = read_manifest_document(&root)? else {
            return Err(TrustConfigLoadError {
                path: root,
                action: "inspect",
                detail: format!(
                    "no such file: it is the workspace root that {} names",
                    member_manifest.display()
                ),
            });
        };
        document
    };
    if !matches!(WorkspaceRole::read(&root, &document)?, WorkspaceRole::Root { .. }) {
        return Err(TrustConfigLoadError {
            path: root,
            action: "validate",
            detail: format!(
                "the workspace root of {} declares no [workspace]",
                member_manifest.display()
            ),
        });
    }
    Ok((root != member_manifest).then_some(root))
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
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n\n[trust]\nlevel = \"L1\"\nbackstop = 2000\n",
        );

        let resolved = resolve_trust_config(root.path(), None).expect("load");
        assert_eq!(resolved.config.level, "L1");
        assert_eq!(
            resolved.config.backstop,
            trust_types::determinism::Backstop { per_mille: 2000 }
        );
        assert_eq!(resolved.config.effort, trust_types::determinism::EffortScale::BUILTIN);
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
        assert!(error.detail.contains("backstop"), "{error}");
    }

    /// One run uses one budget profile: a member table naming `effort` or
    /// `backstop` is refused, and the workspace root's values govern every
    /// member.
    #[test]
    fn the_budgets_are_the_workspace_roots_alone() {
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[workspace]\nmembers = [\"member\"]\n\n[trust]\neffort = 7\nbackstop = 3000\n",
        );
        let member = root.path().join("member");
        write(&member.join("Cargo.toml"), "[package]\nname = \"member\"\n");
        let resolved = resolve_trust_config(&member, None).expect("load");
        assert_eq!(
            resolved.config.effort,
            trust_types::determinism::EffortScale { conflicts_per_node: 7 }
        );
        assert_eq!(
            resolved.config.backstop,
            trust_types::determinism::Backstop { per_mille: 3000 }
        );

        for key in ["effort = 5", "backstop = 500"] {
            write(
                &member.join("Cargo.toml"),
                &format!("[package]\nname = \"member\"\n\n[trust]\n{key}\n"),
            );
            let error = resolve_trust_config(&member, None).expect_err(key);
            assert_eq!(error.action, "validate", "{key}");
            assert!(error.detail.contains("workspace policy"), "{key}: {error}");
        }

        // A manifest that is its own workspace root sets its own budgets, even
        // inside another workspace's directory tree.
        let nested = member.join("nested");
        write(
            &nested.join("Cargo.toml"),
            "[package]\nname = \"nested\"\n\n[workspace]\n\n[trust]\neffort = 5\n",
        );
        let resolved = resolve_trust_config(&nested, None).expect("its own root");
        assert_eq!(
            resolved.config.effort,
            trust_types::determinism::EffortScale { conflicts_per_node: 5 }
        );

        // A workspace root with no [trust] table still owns the budgets.
        write(&root.path().join("Cargo.toml"), "[workspace]\nmembers = [\"member\"]\n");
        let error = resolve_trust_config(&member, None).expect_err("member budget");
        assert!(error.detail.contains("workspace policy"), "{error}");
        write(&member.join("Cargo.toml"), "[package]\nname = \"member\"\n");
        let resolved = resolve_trust_config(&member, None).expect("load");
        assert_eq!(resolved.config.effort, trust_types::determinism::EffortScale::BUILTIN);
        assert_eq!(resolved.config.backstop, trust_types::determinism::Backstop::BUILTIN);
    }

    #[test]
    fn an_unknown_key_in_the_deprecated_file_is_equally_an_error() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("trust.toml"), "levl = \"L1\"\n");

        let error = resolve_trust_config(root.path(), None).expect_err("a typo must fail the load");
        assert_eq!(error.action, "validate");
        assert!(error.detail.contains("unknown field"), "{error}");
    }

    /// One workspace, one policy (plan §3.6; DECISION_QUEUE T7c-4): a member's
    /// own `[trust]` table, of any keys or none, and a `trust.toml` beside it
    /// are refused, naming what they declare and the root to move it to.
    #[test]
    fn a_members_own_policy_is_refused_naming_its_keys_and_the_root() {
        let root = tempfile::tempdir().expect("config fixture");
        let root_manifest = root.path().join("Cargo.toml");
        write(
            &root_manifest,
            "[workspace]\nmembers = [\"member\"]\n\n[trust]\nlevel = \"L0\"\nskip_functions = [\"helper\"]\n",
        );
        let member = root.path().join("member");
        let member_manifest = member.join("Cargo.toml");
        for (table, named) in [
            ("level = \"L1\"\nskip_functions = []\n", "`level`, `skip_functions`"),
            ("", "no keys"),
            ("levl = \"L1\"\n", "`levl`"),
        ] {
            write(&member_manifest, &format!("[package]\nname = \"member\"\n\n[trust]\n{table}"));
            let error = resolve_trust_config(&member, None).expect_err("a member's table");
            assert_eq!(error.action, "validate", "{error}");
            assert_eq!(error.path, member_manifest, "{error}");
            assert!(error.detail.contains(named), "{named}: {error}");
            assert!(error.detail.contains("workspace policy"), "{error}");
            assert!(error.detail.contains(&root_manifest.display().to_string()), "{error}");
        }

        write(&member_manifest, "[package]\nname = \"member\"\n");
        let legacy = member.join(LEGACY_CONFIG_FILE);
        write(&legacy, "level = \"L1\"\n");
        let error = resolve_trust_config(&member, None).expect_err("a member's trust.toml");
        assert_eq!(error.path, legacy, "{error}");
        assert!(error.detail.contains("`level`"), "{error}");
        assert!(error.detail.contains(&root_manifest.display().to_string()), "{error}");

        std::fs::remove_file(&legacy).expect("remove the member's trust.toml");
        let resolved = resolve_trust_config(&member, None).expect("the root's policy");
        assert_eq!(resolved.config.level, "L0");
        assert_eq!(resolved.config.skip_functions, ["helper"]);
        assert_eq!(resolved.source, TrustConfigSource::Manifest(root_manifest));
        assert_eq!(resolved.member_manifest, Some(member_manifest));
    }

    /// A member reads the policy its root reads, the root's deprecated
    /// `trust.toml` included: where a run starts never changes the policy.
    #[test]
    fn a_member_reads_the_policy_its_root_reads() {
        let root = tempfile::tempdir().expect("config fixture");
        write(&root.path().join("Cargo.toml"), "[workspace]\nmembers = [\"member\"]\n");
        write(&root.path().join(LEGACY_CONFIG_FILE), "level = \"L1\"\n");
        let member = root.path().join("member");
        write(&member.join("Cargo.toml"), "[package]\nname = \"member\"\n");

        let from_root = resolve_trust_config(root.path(), None).expect("the root");
        let from_member = resolve_trust_config(&member, None).expect("the member");
        assert_eq!(from_root.config.level, "L1");
        assert_eq!(from_member.config.level, from_root.config.level);
        assert_eq!(from_member.source, from_root.source);
        assert_eq!(from_root.member_manifest, None);
        assert_eq!(from_member.member_manifest, Some(member.join("Cargo.toml")));
        // `targo trust init` scaffolds the table where the policy lives.
        assert_eq!(policy_manifest(&member).expect("search"), Some(root.path().join("Cargo.toml")));
        assert_eq!(
            policy_manifest(root.path()).expect("search"),
            Some(root.path().join("Cargo.toml"))
        );
    }

    /// T7b: `compiler_timeout_secs` is retired into `backstop`. Wherever a
    /// table is policy — a package's own table, its workspace root's, the
    /// deprecated stand-alone file — naming it is refused, and the refusal
    /// names `backstop` and where to set it rather than only "unknown field".
    #[test]
    fn the_retired_compiler_timeout_is_refused_naming_the_backstop() {
        let assert_names_the_replacement = |error: TrustConfigLoadError, declared_in: &Path| {
            assert_eq!(error.action, "validate", "{error}");
            assert_eq!(error.path, declared_in, "{error}");
            assert!(error.detail.contains("`compiler_timeout_secs` was retired"), "{error}");
            assert!(error.detail.contains("`backstop`"), "{error}");
            assert!(error.detail.contains("workspace root"), "{error}");
            assert!(!error.detail.contains("unknown field"), "{error}");
        };

        let root = tempfile::tempdir().expect("config fixture");
        let package = root.path().join("Cargo.toml");
        write(&package, "[package]\nname = \"demo\"\n\n[trust]\ncompiler_timeout_secs = 72000\n");
        let error = resolve_trust_config(root.path(), None).expect_err("a package's own table");
        assert_names_the_replacement(error, &package);

        let workspace = tempfile::tempdir().expect("config fixture");
        let root_manifest = workspace.path().join("Cargo.toml");
        write(
            &root_manifest,
            "[workspace]\nmembers = [\"member\"]\n\n[trust]\ncompiler_timeout_secs = 43200\n",
        );
        let member = workspace.path().join("member");
        write(&member.join("Cargo.toml"), "[package]\nname = \"member\"\n");
        let error = resolve_trust_config(&member, None).expect_err("the workspace root's table");
        assert_names_the_replacement(error, &root_manifest);

        let legacy = tempfile::tempdir().expect("config fixture");
        let legacy_file = legacy.path().join("trust.toml");
        write(&legacy_file, "compiler_timeout_secs = 1000\n");
        let error = resolve_trust_config(legacy.path(), None).expect_err("the deprecated file");
        assert_names_the_replacement(error, &legacy_file);

        // Control: the replacement itself loads, and scales the ceiling.
        write(&package, "[package]\nname = \"demo\"\n\n[trust]\nbackstop = 2500\n");
        let resolved = resolve_trust_config(root.path(), None).expect("backstop loads");
        assert_eq!(resolved.config.backstop.per_mille, 2500);
        assert!(!known_config_keys().contains(&"compiler_timeout_secs"));
    }

    #[test]
    fn a_member_without_a_table_runs_at_the_roots_policy() {
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
        assert_eq!(resolved.member_manifest, None);
    }

    #[test]
    fn a_non_workspace_ancestor_does_not_supply_defaults() {
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[package]\nname=\"outer\"\n\n[trust]\nlevel=\"L0\"\n",
        );
        let inner = root.path().join("inner");
        write(&inner.join("Cargo.toml"), "[package]\nname = \"inner\"\n");

        let resolved = resolve_trust_config(&inner, None).expect("load");
        assert_eq!(resolved.config.level, default_level());
        assert_eq!(resolved.member_manifest, None);
    }

    /// A `[workspace]` that excludes a package is not that package's
    /// workspace (Cargo's `is_excluded`), so its `[trust]` table is neither
    /// policy for the package nor validated on the package's behalf; the search
    /// passes it by, and a workspace further out may still be the root.
    #[test]
    fn an_excluded_package_is_not_governed_by_the_workspace_that_excludes_it() {
        let root = tempfile::tempdir().expect("config fixture");
        let outer = root.path().join("W");
        let package = outer.join("p");
        write(
            &outer.join("Cargo.toml"),
            "[workspace]\nmembers = []\nexclude = [\"p\"]\n\n[trust]\nlevel = \"L0\"\n\
             enabled = false\nskip_functions = [\"f\"]\n",
        );
        write(&package.join("Cargo.toml"), "[package]\nname = \"p\"\n");
        let resolved = resolve_trust_config(&package, None).expect("p is its own root");
        assert_eq!(resolved.config.level, default_level(), "no downgrade from W");
        assert!(resolved.config.enabled);
        assert!(resolved.config.skip_functions.is_empty());
        assert_eq!(resolved.member_manifest, None);

        // W's retired key is W's to fix; p's own table is its root table.
        write(
            &outer.join("Cargo.toml"),
            "[workspace]\nexclude = [\"p\"]\n\n[trust]\nfunction_budget_ms = 100\n",
        );
        write(&package.join("Cargo.toml"), "[package]\nname = \"p\"\n\n[trust]\neffort = 5\n");
        let resolved = resolve_trust_config(&package, None).expect("W's table is not read");
        assert_eq!(
            resolved.config.effort,
            trust_types::determinism::EffortScale { conflicts_per_node: 5 }
        );

        // Listed in `members` as well, p is a member after all.
        write(
            &outer.join("Cargo.toml"),
            "[workspace]\nmembers = [\"p\"]\nexclude = [\"p\"]\n\n[trust]\nlevel = \"L1\"\n",
        );
        write(&package.join("Cargo.toml"), "[package]\nname = \"p\"\n");
        let resolved = resolve_trust_config(&package, None).expect("member");
        assert_eq!(resolved.config.level, "L1");
        assert_eq!(resolved.source, TrustConfigSource::Manifest(outer.join("Cargo.toml")));
        assert_eq!(resolved.member_manifest, Some(package.join("Cargo.toml")));

        // Excluded from W, p is still a member of the workspace above W.
        write(
            &outer.join("Cargo.toml"),
            "[workspace]\nexclude = [\"p\"]\n\n[trust]\nlevel = \"L0\"\n",
        );
        write(
            &root.path().join("Cargo.toml"),
            "[workspace]\nmembers = [\"W/p\"]\n\n[trust]\nlevel = \"L1\"\n",
        );
        let resolved = resolve_trust_config(&package, None).expect("outer root");
        assert_eq!(resolved.config.level, "L1");
        assert_eq!(resolved.source, TrustConfigSource::Manifest(root.path().join("Cargo.toml")));
    }

    /// `package.workspace` names the root (Cargo's `read_root_pointer`), wherever
    /// it is: the root's table is the member's workspace policy, its budgets are
    /// the run's, and the member's own budgets are refused.
    #[test]
    fn a_package_workspace_pointer_names_the_root() {
        let root = tempfile::tempdir().expect("config fixture");
        let workspace = root.path().join("R");
        let member = root.path().join("m");
        write(
            &workspace.join("Cargo.toml"),
            "[workspace]\nmembers = [\"../m\"]\n\n[trust]\nlevel = \"L1\"\neffort = 7\n",
        );
        write(&member.join("Cargo.toml"), "[package]\nname = \"m\"\nworkspace = \"../R\"\n");
        let resolved = resolve_trust_config(&member, None).expect("load");
        assert_eq!(resolved.config.level, "L1");
        assert_eq!(
            resolved.config.effort,
            trust_types::determinism::EffortScale { conflicts_per_node: 7 }
        );
        assert_eq!(resolved.source, TrustConfigSource::Manifest(workspace.join("Cargo.toml")));

        // A package beneath a pointer member is pointed at the same root.
        let nested = member.join("inner");
        write(&nested.join("Cargo.toml"), "[package]\nname = \"inner\"\n");
        let resolved = resolve_trust_config(&nested, None).expect("load");
        assert_eq!(resolved.source, TrustConfigSource::Manifest(workspace.join("Cargo.toml")));
        assert_eq!(resolved.member_manifest, Some(nested.join("Cargo.toml")));

        write(
            &member.join("Cargo.toml"),
            "[package]\nname = \"m\"\nworkspace = \"../R\"\n\n[trust]\neffort = 5\nbackstop = 2000\n",
        );
        let error = resolve_trust_config(&member, None).expect_err("member budget");
        assert!(error.detail.contains("workspace policy"), "{error}");

        // A pointer to a manifest that is not a workspace root, or to none.
        write(&member.join("Cargo.toml"), "[package]\nname = \"m\"\nworkspace = \"../R\"\n");
        write(&workspace.join("Cargo.toml"), "[package]\nname = \"r\"\n");
        let error = resolve_trust_config(&member, None).expect_err("not a root");
        assert_eq!(error.path, workspace.join("Cargo.toml"));
        assert!(error.detail.contains("declares no [workspace]"), "{error}");
        write(&member.join("Cargo.toml"), "[package]\nname = \"m\"\nworkspace = \"../gone\"\n");
        let error = resolve_trust_config(&member, None).expect_err("no root");
        assert_eq!(error.path, root.path().join("gone/Cargo.toml"));
    }

    /// The search stops where Cargo's does, after `CARGO_HOME` and at a
    /// `target/package` directory, and an ancestor manifest it cannot read is
    /// an error rather than a manifest passed over.
    #[test]
    fn the_root_search_stops_where_cargos_does() {
        let root = tempfile::tempdir().expect("config fixture");
        let root_manifest = root.path().join("Cargo.toml");
        write(&root_manifest, "[workspace]\n\n[trust]\nlevel = \"L1\"\n");
        let home = root.path().join("home");
        let dependency = home.join("registry/src/index/dep/Cargo.toml");
        write(&dependency, "[package]\nname = \"dep\"\n");
        let found = member_workspace_root(&dependency, None).expect("search");
        assert_eq!(found, Some(root_manifest.clone()));
        let found = member_workspace_root(&dependency, Some(&home)).expect("search");
        assert!(found.is_none(), "the search does not cross CARGO_HOME");

        let packaged = root.path().join("target/package/p-0.1.0/Cargo.toml");
        write(&packaged, "[package]\nname = \"p\"\n");
        let found = member_workspace_root(&packaged, None).expect("search");
        assert!(found.is_none(), "the search stops at target/package");

        write(&root.path().join("mid/Cargo.toml"), "[package\n");
        let package = root.path().join("mid/x/p/Cargo.toml");
        write(&package, "[package]\nname = \"p\"\n");
        let error = member_workspace_root(&package, None).expect_err("broken ancestor");
        assert_eq!(error.path, root.path().join("mid/Cargo.toml"));
        assert!(error.detail.contains("workspace-root search"), "{error}");
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
        write(
            &root.path().join("Cargo.toml"),
            "[package]\nname=\"d\"\n\n[trust]\nlevel = \"L9\"\n",
        );

        let error = resolve_trust_config(root.path(), None).expect_err("bad level must fail");
        assert!(error.detail.contains("invalid verification level"), "{error}");
    }

    #[test]
    fn an_out_of_domain_budget_is_rejected() {
        for (key, needle) in [
            ("effort = 0", "outside 1..="),
            ("effort = 400001", "outside 1..="),
            ("backstop = 0", "at least 1 per mille"),
        ] {
            let root = tempfile::tempdir().expect("config fixture");
            write(
                &root.path().join("Cargo.toml"),
                &format!("[package]\nname=\"d\"\n\n[trust]\n{key}\n"),
            );
            let error = resolve_trust_config(root.path(), None).expect_err(key);
            assert!(error.detail.contains(needle), "{key}: {error}");
        }
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
    fn an_unregistered_trust_profile_is_rejected() {
        // The silent-profile-downgrade case, at the config surface: the label
        // was accepted, hardened mode was switched ON for it, the banner
        // announced it by name, and the compiler generated zero hardened
        // obligations because the registry does not know it.
        // NOT in this list: `" unix-hardened "`. Separator, case and
        // surrounding whitespace are spelling, and the registry canonicalizes
        // them — see `every_registered_trust_profile_loads_in_the_registry_spelling`.
        for label in ["unix_hardened_v2", "unix_hardend", "unix", "release", "hardenedness"] {
            let root = tempfile::tempdir().expect("config fixture");
            write(
                &root.path().join("Cargo.toml"),
                &format!("[package]\nname=\"d\"\n\n[trust]\ntrust_profile = \"{label}\"\n"),
            );

            let Err(error) = resolve_trust_config(root.path(), None) else {
                panic!("unregistered profile `{label}` must fail the load");
            };
            assert_eq!(error.action, "validate", "{label}");
            assert!(error.detail.contains("unknown trust profile"), "{label}: {error}");
            assert!(error.detail.contains("unix_hardened"), "{label}: {error}");
            assert!(error.detail.contains("hardened = false"), "{label}: {error}");
        }
    }

    #[test]
    fn every_registered_trust_profile_loads_in_the_registry_spelling() {
        for registered in trust_vcgen::known_hardened_profiles() {
            for spelling in
                [registered.to_string(), registered.to_uppercase(), registered.replace('_', "-")]
            {
                let root = tempfile::tempdir().expect("config fixture");
                write(
                    &root.path().join("Cargo.toml"),
                    &format!("[package]\nname=\"d\"\n\n[trust]\ntrust_profile = \"{spelling}\"\n"),
                );

                let resolved = resolve_trust_config(root.path(), None)
                    .unwrap_or_else(|error| panic!("{spelling} must load: {error}"));
                assert_eq!(resolved.config.trust_profile.as_deref(), Some(*registered));
            }
        }
    }

    #[test]
    fn hardened_false_is_still_the_documented_opt_out() {
        // `hardened = false` is an explicit choice, not a typo, and refusing
        // unregistered LABELS must not have touched it. It is also accepted
        // beside a registered label, which is the shape the opt-out actually
        // takes in a project that has one committed.
        let root = tempfile::tempdir().expect("config fixture");
        write(
            &root.path().join("Cargo.toml"),
            "[package]\nname=\"d\"\n\n[trust]\nhardened = false\ntrust_profile = \"coreutils_hardened\"\n",
        );

        let resolved = resolve_trust_config(root.path(), None).expect("opt-out must load");
        assert_eq!(resolved.config.hardened, Some(false));
        assert_eq!(resolved.config.trust_profile.as_deref(), Some("coreutils_hardened"));
    }

    /// S9: the trust-mc engine is never a targo-selectable codegen backend. It
    /// reaches trustc only as an explicitly selected external backend in its
    /// own session, never through `[trust] codegen_backend` or
    /// `--codegen-backend`.
    #[test]
    fn the_trust_mc_engine_backend_is_not_a_selectable_codegen_backend() {
        for name in [
            "trust-mc",
            "trust_mc",
            "TRUST_MC",
            " trust_mc ",
            "trust_mc-ay",
            "librustc_codegen_trust_mc.dylib",
            "/abs/librustc_codegen_trust_mc.dylib",
        ] {
            assert_eq!(normalize_codegen_backend(name), None, "{name:?} was accepted");
            assert!(
                !known_codegen_backend_names()
                    .iter()
                    .any(|known| known.eq_ignore_ascii_case(name.trim())),
                "{name:?} is listed as a known backend"
            );
        }
        for name in ["trust_mc", "/abs/librustc_codegen_trust_mc.dylib"] {
            let root = tempfile::tempdir().expect("config fixture");
            write(
                &root.path().join("Cargo.toml"),
                &format!("[package]\nname=\"d\"\n\n[trust]\ncodegen_backend = \"{name}\"\n"),
            );
            let error = resolve_trust_config(root.path(), None)
                .expect_err("a trust-mc backend in [trust] must fail");
            assert!(error.detail.contains("unknown codegen backend"), "{error}");
        }
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

        let error =
            resolve_trust_config(root.path(), None).expect_err("oversized config must fail closed");
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

        let error =
            resolve_trust_config(root.path(), None).expect_err("symlinked config must fail closed");
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

    /// Trust (platform protocols, plan L1a; FC-7 for `[trust]` keys), adversarial: L1a adds the
    /// `-Ztrust-platform-*` compiler options and the TRUSTFLAGS route, but no `[trust]` key (plan
    /// L5b adds `platform_properties`, `platform_premises` and `platform_unanalysed`). Until then
    /// a project that writes a platform policy into its manifest must be told it does nothing,
    /// on every surface the table is read from: the member manifest, `Targo.toml`, the
    /// workspace root a member inherits from, and the deprecated stand-alone file. Snake and
    /// kebab spellings alike, and the design's names that no landing has scheduled as keys.
    #[test]
    fn platform_policy_keys_are_refused_until_targo_transports_them() {
        const KEYS: &[(&str, &str)] = &[
            ("platform_properties", "[\"fd-inherit\"]"),
            ("platform-properties", "[\"fd-inherit\"]"),
            ("platform_properties", "\"fd-inherit\""),
            ("platform_unanalysed", "\"deny\""),
            ("platform_unanalyzed", "\"deny\""),
            ("platform_budget", "1000000"),
            ("platform_report", "\"verbose\""),
            ("platform_premises", "[\"fd-bound\"]"),
            ("platform_dump_facts", "\"facts.sidecar\""),
            ("platform", "{ properties = [\"fd-inherit\"] }"),
        ];
        for (key, value) in KEYS {
            let entry = format!("{key} = {value}\n");
            let refused = |error: TrustConfigLoadError, surface: &str| {
                assert_eq!(error.action, "validate", "{surface} `{entry}`: {error}");
                assert!(error.detail.contains("unknown field"), "{surface} `{entry}`: {error}");
                assert!(error.detail.contains(&format!("`{key}`")), "{surface} `{entry}`: {error}");
            };

            for manifest in MANIFEST_NAMES {
                let root = tempfile::tempdir().expect("config fixture");
                write(
                    &root.path().join(manifest),
                    &format!("[package]\nname = \"d\"\n\n[trust]\nlevel = \"L1\"\n{entry}"),
                );
                let error = resolve_trust_config(root.path(), None)
                    .expect_err("a platform key in the member manifest must fail the load");
                refused(error, manifest);
            }

            let root = tempfile::tempdir().expect("config fixture");
            write(
                &root.path().join("Cargo.toml"),
                &format!("[workspace]\nmembers = [\"member\"]\n\n[trust]\n{entry}"),
            );
            let member = root.path().join("member");
            write(&member.join("Cargo.toml"), "[package]\nname = \"member\"\n");
            let error = resolve_trust_config(&member, None)
                .expect_err("a platform key in the workspace root must fail the member's load");
            refused(error, "workspace root");

            let root = tempfile::tempdir().expect("config fixture");
            write(&root.path().join(LEGACY_CONFIG_FILE), &entry);
            let error = resolve_trust_config(root.path(), None)
                .expect_err("a platform key in the deprecated file must fail the load");
            refused(error, LEGACY_CONFIG_FILE);
        }
    }
}
