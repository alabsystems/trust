//! Trust product version identity for `targo trust version`.
//!
//! # The Trust version line
//!
//! Trust versions are `major.minor.dev` and have nothing to do with Rust's
//! version line. Andrew's constellation scheme (`alabsystems/publication`)
//! gives the three components these meanings:
//!
//! * **major** — the top-level line.
//! * **minor** — the release counter. A public release is always `X.Y.0`.
//! * **dev** — the internal iteration counter. `dev == 0` is a public
//!   version; `dev > 0` marks internal-only work that is never what a public
//!   release is called. After `X.Y.0` ships, internal work bumps `dev`; the
//!   next public release bumps `minor` (or `major`) and resets `dev` to 0.
//!
//! There are no prerelease or build suffixes: `0.1.0-preview.1` is not a Trust
//! version, it is a semver habit inherited from elsewhere. The dev counter
//! already says "not public", so a suffix would be a second, weaker way to say
//! the same thing.
//!
//! # Rust alignment is a record, never an authority
//!
//! Trust began as a fork of `rust-lang/rust`, and [`RustAlignment`] records the
//! exact upstream revision last merged in so compatibility work has a fixed
//! anchor. It is evidence *about* the checkout — nothing derives Trust's own
//! version, channel, or release identity from it.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fmt::{self, Write as _};

use serde::{Deserialize, Serialize};

/// Schema marker for `targo trust version --json`.
pub const VERSION_SCHEMA: &str = "trust.version.v3";

/// Schema marker for the checked-in source file.
pub const VERSION_SOURCE_SCHEMA: &str = "trust.version-source.v2";

/// Channel name for a public version (`dev == 0`).
pub const CHANNEL_RELEASE: &str = "release";

/// Channel name for an internal iteration (`dev > 0`).
pub const CHANNEL_DEV: &str = "dev";

/// Default source path for checked-in Trust product version metadata.
pub const DEFAULT_VERSION_SOURCE_PATH: &str = "release/trust-version.toml";

fn default_version_schema() -> String {
    VERSION_SCHEMA.to_string()
}

fn deserialize_version_schema<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let schema = String::deserialize(deserializer)?;
    match schema.as_str() {
        VERSION_SCHEMA => Ok(VERSION_SCHEMA.to_string()),
        _ => Err(serde::de::Error::custom(format!(
            "unsupported Trust version identity schema `{schema}`"
        ))),
    }
}

fn deserialize_schema_registry<'de, D>(
    deserializer: D,
) -> Result<BTreeMap<String, String>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let schemas = BTreeMap::<String, String>::deserialize(deserializer)?;
    match schemas.get("version").map(String::as_str) {
        Some(VERSION_SCHEMA) => {}
        Some(schema) => {
            return Err(serde::de::Error::custom(format!(
                "unsupported Trust version registry schema `{schema}`"
            )));
        }
        None => {
            return Err(serde::de::Error::custom(
                "Trust version identity is missing `schemas.version`",
            ));
        }
    }
    Ok(schemas)
}

/// A Trust version: `major.minor.dev`, exactly three numbers, no suffix.
///
/// See the crate docs for what the three components mean. The only derived
/// property is the channel: `dev == 0` is [`CHANNEL_RELEASE`], anything else is
/// [`CHANNEL_DEV`]. Nothing else in the toolchain may author a channel, so a
/// version and its channel cannot disagree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct TrustVersion {
    pub major: u32,
    pub minor: u32,
    pub dev: u32,
}

impl TrustVersion {
    /// Parse `major.minor.dev`. Rejects prerelease/build suffixes outright —
    /// the dev counter is how Trust says "not public".
    pub fn parse(version: &str) -> Result<Self, VersionError> {
        let invalid =
            || VersionError::InvalidProductVersion { version: version.trim().to_string() };
        let version = version.trim();
        if version.contains(['-', '+']) {
            return Err(invalid());
        }
        let mut parts = version.split('.');
        let mut next = || -> Result<u32, VersionError> {
            let part = parts.next().ok_or_else(invalid)?;
            if part.is_empty() || !part.bytes().all(|byte| byte.is_ascii_digit()) {
                return Err(invalid());
            }
            part.parse().map_err(|_| invalid())
        };
        let (major, minor, dev) = (next()?, next()?, next()?);
        if parts.next().is_some() {
            return Err(invalid());
        }
        Ok(Self { major, minor, dev })
    }

    /// True when this is a version a public release may be called.
    #[must_use]
    pub fn is_public(&self) -> bool {
        self.dev == 0
    }

    /// [`CHANNEL_RELEASE`] or [`CHANNEL_DEV`], derived from the dev counter.
    #[must_use]
    pub fn channel(&self) -> &'static str {
        if self.is_public() { CHANNEL_RELEASE } else { CHANNEL_DEV }
    }
}

impl fmt::Display for TrustVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.dev)
    }
}

/// The upstream `rust-lang/rust` revision Trust last merged.
///
/// Trust is its own toolchain on its own version line; this table exists so
/// compatibility work has a fixed anchor to diff against, and so a reader can
/// tell how old that anchor is. It confers no authority: no Trust version,
/// channel, gate, or proof claim is derived from it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RustAlignment {
    /// The upstream release the merged revision belonged to, e.g. `1.99.0`.
    pub rustc_version: String,
    /// `rust-lang/rust:<40-hex>` — the exact revision merged.
    pub revision: String,
    /// ISO date of that merge, for staleness at a glance.
    pub merged_on: String,
}

impl RustAlignment {
    fn validate(&self) -> Result<(), VersionError> {
        if !is_dotted_numeric(&self.rustc_version) {
            return Err(VersionError::InvalidRustAlignment {
                field: "rustc_version",
                value: self.rustc_version.clone(),
            });
        }
        if !is_plausible_upstream_revision(&self.revision) {
            return Err(VersionError::InvalidRustAlignment {
                field: "revision",
                value: self.revision.clone(),
            });
        }
        if !is_iso_date(&self.merged_on) {
            return Err(VersionError::InvalidRustAlignment {
                field: "merged_on",
                value: self.merged_on.clone(),
            });
        }
        Ok(())
    }
}

/// Human-authored Trust version source.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustVersionSource {
    pub schema_version: String,
    pub product: String,
    pub toolchain_alias: String,
    pub trust_product_version: String,
    pub release_report_schema: String,
    pub rust_alignment: RustAlignment,
    #[serde(default)]
    pub schemas: BTreeMap<String, String>,
}

impl TrustVersionSource {
    /// The parsed Trust version. Only callable after [`Self::validate`].
    pub fn version(&self) -> Result<TrustVersion, VersionError> {
        TrustVersion::parse(&self.trust_product_version)
    }

    pub fn validate(&self) -> Result<(), VersionError> {
        if self.schema_version != VERSION_SOURCE_SCHEMA {
            return Err(VersionError::InvalidSourceSchema { found: self.schema_version.clone() });
        }
        self.version()?;
        if self.product.trim().is_empty() {
            return Err(VersionError::MissingField("product"));
        }
        if self.toolchain_alias.trim().is_empty() {
            return Err(VersionError::MissingField("toolchain_alias"));
        }
        if let Some(found) = self.schemas.get("version")
            && found != VERSION_SCHEMA
        {
            return Err(VersionError::InvalidRegisteredVersionSchema { found: found.clone() });
        }
        self.rust_alignment.validate()
    }
}

/// Runtime identity fields derived from the candidate checkout/toolchain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VersionRuntime {
    pub rust_upstream_version: String,
    pub bootstrap_channel: String,
    pub rust_compat_version: String,
    pub rust_compat_source: String,
    pub archive_version: String,
    pub candidate_commit: Option<String>,
    pub commit_date: Option<String>,
    pub host: String,
    pub runner_kind: String,
    pub candidate_command: String,
    pub candidate_command_version: u32,
    pub tools: BoundTools,
    pub stage0: Option<Stage0Info>,
}

/// Identity for one executable participating in the Trust command surface.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundToolIdentity {
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub executable: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub version: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub commit_hash: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rust_compat_version: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub resolution: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rejected_inherited_name: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rejected_path: Option<String>,
}

impl BoundToolIdentity {
    #[must_use]
    pub fn missing(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            path: None,
            sha256: None,
            executable: None,
            version: None,
            commit_hash: None,
            rust_compat_version: None,
            resolution: Some("not-found".to_string()),
            rejected_inherited_name: None,
            rejected_path: None,
        }
    }

    #[must_use]
    pub fn rejected_inherited(
        name: impl Into<String>,
        inherited_name: impl Into<String>,
        inherited_path: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            path: None,
            sha256: None,
            executable: None,
            version: None,
            commit_hash: None,
            rust_compat_version: None,
            resolution: Some("forbidden-inherited-rust-name".to_string()),
            rejected_inherited_name: Some(inherited_name.into()),
            rejected_path: Some(inherited_path.into()),
        }
    }

    #[must_use]
    pub fn has_bound_path(&self) -> bool {
        self.path.as_deref().is_some_and(|path| !path.trim().is_empty())
    }

    #[must_use]
    pub fn has_forbidden_inherited_evidence(&self) -> bool {
        self.resolution.as_deref() == Some("forbidden-inherited-rust-name")
    }
}

fn missing_trustdoc_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("trustdoc")
}

fn missing_trustfmt_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("trustfmt")
}

fn missing_targo_fmt_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("targo-fmt") // Trust: produced component is targo-fmt
}

fn missing_tippy_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("tippy")
}

fn missing_targo_tippy_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("targo-tippy")
}

fn missing_tippy_driver_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("tippy-driver")
}

fn missing_trust_analyzer_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("trust-analyzer")
}

fn missing_trustd_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("trustd")
}

fn missing_trust_miri_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("trust-miri")
}

fn missing_targo_miri_bound_tool() -> BoundToolIdentity {
    BoundToolIdentity::missing("targo-miri") // Trust: produced component is targo-miri
}

/// Bound identities for the canonical Trust command surface.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundTools {
    pub frontend: BoundToolIdentity,
    pub extension: BoundToolIdentity,
    pub compiler: BoundToolIdentity,
    #[serde(default = "missing_trustdoc_bound_tool")]
    pub documentation: BoundToolIdentity,
    #[serde(default = "missing_trustfmt_bound_tool")]
    pub formatter: BoundToolIdentity,
    #[serde(default = "missing_targo_fmt_bound_tool")]
    pub cargo_formatter: BoundToolIdentity,
    #[serde(default = "missing_tippy_bound_tool")]
    pub tippy: BoundToolIdentity,
    #[serde(default = "missing_targo_tippy_bound_tool", alias = "clippy")]
    pub targo_tippy: BoundToolIdentity,
    #[serde(default = "missing_tippy_driver_bound_tool", alias = "clippy_driver")]
    pub tippy_driver: BoundToolIdentity,
    #[serde(default = "missing_trust_analyzer_bound_tool")]
    pub analyzer: BoundToolIdentity,
    #[serde(default = "missing_trustd_bound_tool")]
    pub daemon: BoundToolIdentity,
    #[serde(default = "missing_trust_miri_bound_tool")]
    pub miri: BoundToolIdentity,
    #[serde(default = "missing_targo_miri_bound_tool")]
    pub targo_miri: BoundToolIdentity,
}

impl BoundTools {
    #[must_use]
    pub fn required(&self) -> [&BoundToolIdentity; 11] {
        [
            &self.frontend,
            &self.extension,
            &self.compiler,
            &self.documentation,
            &self.formatter,
            &self.cargo_formatter,
            &self.tippy,
            &self.targo_tippy,
            &self.tippy_driver,
            &self.analyzer,
            &self.daemon,
        ]
    }

    #[must_use]
    pub fn optional(&self) -> [&BoundToolIdentity; 2] {
        [&self.miri, &self.targo_miri]
    }

    #[must_use]
    pub fn all(&self) -> [&BoundToolIdentity; 13] {
        [
            &self.frontend,
            &self.extension,
            &self.compiler,
            &self.documentation,
            &self.formatter,
            &self.cargo_formatter,
            &self.tippy,
            &self.targo_tippy,
            &self.tippy_driver,
            &self.analyzer,
            &self.daemon,
            &self.miri,
            &self.targo_miri,
        ]
    }
}

/// Stage0 bootstrap identity.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Stage0Info {
    pub source: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub channel_manifest_sha256: Option<String>,
}

/// Complete `targo trust version --json` payload.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TrustVersionIdentity {
    #[serde(default = "default_version_schema", deserialize_with = "deserialize_version_schema")]
    pub schema_version: String,
    pub product: String,
    pub toolchain_alias: String,
    pub trust_product_version: String,
    pub trust_product_channel: String,
    pub rust_upstream_version: String,
    pub bootstrap_channel: String,
    pub rust_compat_version: String,
    pub rust_compat_source: String,
    pub archive_version: String,
    pub rust_alignment: RustAlignment,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub candidate_commit: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub commit_date: Option<String>,
    pub host: String,
    pub runner_kind: String,
    pub candidate_command: String,
    pub candidate_command_version: u32,
    pub tools: BoundTools,
    #[serde(deserialize_with = "deserialize_schema_registry")]
    pub schemas: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stage0: Option<Stage0Info>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub components: Vec<String>,
}

impl TrustVersionIdentity {
    #[must_use]
    pub fn from_source_and_runtime(source: TrustVersionSource, runtime: VersionRuntime) -> Self {
        // The channel is derived, never authored: a version and its channel
        // cannot disagree if only one of them is written down. An unparseable
        // version cannot reach here — `validate` runs first — but if it somehow
        // did, `dev` is unknown, so the honest answer is the non-public one.
        let channel =
            source.version().map_or(CHANNEL_DEV, |version| version.channel()).to_string();

        let mut schemas = source.schemas;
        schemas.insert("version".to_string(), VERSION_SCHEMA.to_string());
        schemas.entry("release_report".to_string()).or_insert(source.release_report_schema.clone());

        Self {
            schema_version: VERSION_SCHEMA.to_string(),
            product: source.product,
            toolchain_alias: source.toolchain_alias,
            trust_product_version: source.trust_product_version,
            trust_product_channel: channel,
            rust_upstream_version: runtime.rust_upstream_version,
            bootstrap_channel: runtime.bootstrap_channel,
            rust_compat_version: runtime.rust_compat_version,
            rust_compat_source: runtime.rust_compat_source,
            archive_version: runtime.archive_version,
            rust_alignment: source.rust_alignment,
            candidate_commit: runtime.candidate_commit,
            commit_date: runtime.commit_date,
            host: runtime.host,
            runner_kind: runtime.runner_kind,
            candidate_command: runtime.candidate_command,
            candidate_command_version: runtime.candidate_command_version,
            tools: runtime.tools,
            schemas,
            stage0: runtime.stage0,
            components: Vec::new(),
        }
    }

    #[must_use]
    pub fn render_text(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "{} {}", self.product, self.trust_product_version);
        let _ = writeln!(out, "rust-compat: {}", self.rust_compat_version);
        let _ = writeln!(out, "toolchain: {}", self.toolchain_alias);
        if let Some(commit) = &self.candidate_commit {
            let _ = writeln!(out, "candidate: {commit}");
        }
        let _ = writeln!(out, "runner: {}", self.runner_kind);
        for tool in self.tools.required() {
            let _ = writeln!(out, "{}: {}", tool.name, display_tool(tool));
        }
        for tool in self.tools.optional() {
            let _ = writeln!(out, "{}: {}", tool.name, display_tool(tool));
        }
        if let Some(verifier_api) = self.schemas.get("verifier_api") {
            let _ = writeln!(out, "verifier-api: {verifier_api}");
        }
        if let Some(release_report) = self.schemas.get("release_report") {
            let _ = writeln!(out, "release-report: {release_report}");
        }
        out
    }

    pub fn render_json_pretty(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }
}

fn display_tool(tool: &BoundToolIdentity) -> String {
    let mut text = tool.name.clone();
    if let Some(version) = &tool.version {
        let _ = write!(text, " {version}");
    }
    if let Some(commit) = &tool.commit_hash {
        let _ = write!(text, " ({commit})");
    }
    if let Some(resolution) = &tool.resolution {
        let _ = write!(text, " [{resolution}]");
    }
    text
}

pub fn parse_version_source(input: &str) -> Result<TrustVersionSource, VersionError> {
    let source: TrustVersionSource = toml::from_str(input)?;
    source.validate()?;
    Ok(source)
}

#[derive(Debug)]
pub enum VersionError {
    Toml(toml::de::Error),
    InvalidSourceSchema { found: String },
    InvalidRegisteredVersionSchema { found: String },
    InvalidProductVersion { version: String },
    MissingField(&'static str),
    InvalidRustAlignment { field: &'static str, value: String },
}

impl fmt::Display for VersionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Toml(source) => write!(f, "failed to parse Trust version source: {source}"),
            Self::InvalidSourceSchema { found } => {
                write!(f, "invalid Trust version source schema {found:?}")
            }
            Self::InvalidRegisteredVersionSchema { found } => {
                write!(f, "Trust version source registers {found:?}, expected {VERSION_SCHEMA:?}")
            }
            Self::InvalidProductVersion { version } => {
                write!(
                    f,
                    "invalid Trust product version {version:?}: Trust versions are \
                     major.minor.dev, three numbers and no suffix (dev = 0 is public, \
                     dev > 0 is internal)"
                )
            }
            Self::MissingField(field) => write!(f, "missing Trust version source field {field}"),
            Self::InvalidRustAlignment { field, value } => {
                write!(f, "invalid rust_alignment.{field} {value:?}")
            }
        }
    }
}

impl std::error::Error for VersionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Toml(source) => Some(source),
            Self::InvalidSourceSchema { .. }
            | Self::InvalidRegisteredVersionSchema { .. }
            | Self::InvalidProductVersion { .. }
            | Self::MissingField(_)
            | Self::InvalidRustAlignment { .. } => None,
        }
    }
}

impl From<toml::de::Error> for VersionError {
    fn from(source: toml::de::Error) -> Self {
        Self::Toml(source)
    }
}

/// A dotted numeric version with at least two components — loose on purpose,
/// because this describes *Rust's* version line, which Trust does not govern.
fn is_dotted_numeric(value: &str) -> bool {
    let value = value.trim();
    let parts: Vec<&str> = value.split('.').collect();
    parts.len() >= 2
        && parts
            .iter()
            .all(|part| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit()))
}

fn is_plausible_upstream_revision(value: &str) -> bool {
    let value = value.trim();
    if value.eq_ignore_ascii_case("unknown") || value.is_empty() {
        return false;
    }
    let commit = value.rsplit_once(':').map_or(value, |(_, commit)| commit);
    commit.len() == 40 && commit.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn is_iso_date(value: &str) -> bool {
    let value = value.trim();
    value.len() == 10
        && value.as_bytes()[4] == b'-'
        && value.as_bytes()[7] == b'-'
        && value
            .bytes()
            .enumerate()
            .all(|(index, byte)| matches!(index, 4 | 7) || byte.is_ascii_digit())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source_text(version: &str) -> String {
        format!(
            r#"
schema_version = "trust.version-source.v2"
product = "Trust"
toolchain_alias = "trust"
trust_product_version = "{version}"
release_report_schema = "trust.release-report.v1"

[rust_alignment]
rustc_version = "1.99.0"
revision = "rust-lang/rust:5e91de65d75d3c849c643f5079509b9e5985a5c0"
merged_on = "2026-07-08"

[schemas]
version = "trust.version.v3"
release_report = "trust.release-report.v1"
verifier_api = "trust.verifier-api.v1"
verifier_run_manifest = "trust.verifier-run-manifest.v1"
"#
        )
    }

    #[test]
    fn trust_version_parses_major_minor_dev() {
        let version = TrustVersion::parse("0.1.0").unwrap();
        assert_eq!(version, TrustVersion { major: 0, minor: 1, dev: 0 });
        assert!(version.is_public());
        assert_eq!(version.channel(), CHANNEL_RELEASE);
        assert_eq!(version.to_string(), "0.1.0");
    }

    #[test]
    fn nonzero_dev_component_is_internal_only() {
        let version = TrustVersion::parse("0.1.7").unwrap();
        assert!(!version.is_public(), "dev > 0 is never what a public release is called");
        assert_eq!(version.channel(), CHANNEL_DEV);
    }

    #[test]
    fn prerelease_suffixes_are_not_trust_versions() {
        // The dev counter is how Trust says "not public"; a suffix would be a
        // second, weaker way to say the same thing.
        for rejected in ["0.1.0-preview.1", "0.1.0-rc1", "0.1.0+build", "0.1", "0.1.0.1", "x.y.z"] {
            assert!(
                TrustVersion::parse(rejected).is_err(),
                "{rejected:?} must not parse as a Trust version"
            );
        }
    }

    #[test]
    fn channel_is_derived_from_the_version_not_authored() {
        let internal = parse_version_source(&source_text("0.1.4")).unwrap();
        let identity = TrustVersionIdentity::from_source_and_runtime(internal, runtime());
        assert_eq!(identity.trust_product_channel, CHANNEL_DEV);

        let public = parse_version_source(&source_text("0.2.0")).unwrap();
        let identity = TrustVersionIdentity::from_source_and_runtime(public, runtime());
        assert_eq!(identity.trust_product_channel, CHANNEL_RELEASE);
    }

    #[test]
    fn rust_alignment_is_validated_but_confers_no_authority() {
        let source = parse_version_source(&source_text("0.1.0")).unwrap();
        assert_eq!(source.rust_alignment.rustc_version, "1.99.0");
        assert_eq!(source.rust_alignment.merged_on, "2026-07-08");
        // The Trust version is 0.1.0 regardless of what Rust calls itself.
        assert_eq!(source.version().unwrap().to_string(), "0.1.0");

        let bad = source_text("0.1.0").replace("2026-07-08", "July 2026");
        assert!(matches!(
            parse_version_source(&bad),
            Err(VersionError::InvalidRustAlignment { field: "merged_on", .. })
        ));
    }

    fn repo_root() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    #[test]
    fn the_checked_in_version_source_is_valid() {
        let text = std::fs::read_to_string(repo_root().join(DEFAULT_VERSION_SOURCE_PATH))
            .expect("release/trust-version.toml must exist");
        let source = parse_version_source(&text).expect("checked-in version source must validate");
        assert_eq!(source.product, "Trust");
        source.version().expect("checked-in version must be major.minor.dev");
    }

    #[test]
    fn the_three_checked_in_version_files_agree() {
        // Trust carries two version lines on purpose, and each has exactly one
        // file that states it. This test is what stops them drifting:
        //   src/version              Trust's own major.minor.dev
        //   src/rust-compat-version  the Rust release the `-V` protocol reports
        // Both must match what release/trust-version.toml — the authoritative
        // record — says they are.
        let root = repo_root();
        let source = parse_version_source(
            &std::fs::read_to_string(root.join(DEFAULT_VERSION_SOURCE_PATH)).unwrap(),
        )
        .unwrap();

        let src_version = std::fs::read_to_string(root.join("src/version"))
            .expect("src/version must exist")
            .trim()
            .to_string();
        assert_eq!(
            src_version, source.trust_product_version,
            "src/version must equal release/trust-version.toml trust_product_version"
        );

        let compat = std::fs::read_to_string(root.join("src/rust-compat-version"))
            .expect("src/rust-compat-version must exist")
            .trim()
            .to_string();
        assert_eq!(
            compat, source.rust_alignment.rustc_version,
            "src/rust-compat-version must equal release/trust-version.toml \
             rust_alignment.rustc_version"
        );
    }

    fn runtime() -> VersionRuntime {
        VersionRuntime {
            rust_upstream_version: "1.96.0".to_string(),
            bootstrap_channel: "trust".to_string(),
            rust_compat_version: "1.96.0-dev".to_string(),
            rust_compat_source: "trustc -Vv release".to_string(),
            archive_version: "1.96.0-trust".to_string(),
            candidate_commit: Some("abcdef1234567890".to_string()),
            commit_date: Some("2026-04-30".to_string()),
            host: "aarch64-apple-darwin".to_string(),
            runner_kind: "candidate-stage2".to_string(),
            candidate_command: "targo trust version --json".to_string(),
            candidate_command_version: 1,
            tools: BoundTools {
                frontend: BoundToolIdentity {
                    name: "targo".to_string(),
                    path: Some("stage2/bin/targo".to_string()),
                    sha256: Some("a".repeat(64)),
                    executable: Some(true),
                    version: Some("1.96.0-dev".to_string()),
                    commit_hash: None,
                    rust_compat_version: None,
                    resolution: Some("sibling-of-targo-trust".to_string()),
                    rejected_inherited_name: None,
                    rejected_path: None,
                },
                extension: BoundToolIdentity {
                    name: "targo-trust".to_string(),
                    path: Some("stage2/bin/targo-trust".to_string()),
                    sha256: Some("b".repeat(64)),
                    executable: Some(true),
                    version: Some("0.1.0".to_string()),
                    commit_hash: Some("abcdef1234567890".to_string()),
                    rust_compat_version: None,
                    resolution: Some("current-exe".to_string()),
                    rejected_inherited_name: None,
                    rejected_path: None,
                },
                compiler: BoundToolIdentity {
                    name: "trustc".to_string(),
                    path: Some("stage2/bin/trustc".to_string()),
                    sha256: Some("c".repeat(64)),
                    executable: Some(true),
                    version: Some("1.96.0-dev".to_string()),
                    commit_hash: Some("abcdef1234567890".to_string()),
                    rust_compat_version: Some("1.96.0-dev".to_string()),
                    resolution: Some("sibling-of-targo-trust".to_string()),
                    rejected_inherited_name: None,
                    rejected_path: None,
                },
                documentation: BoundToolIdentity::missing("trustdoc"),
                formatter: BoundToolIdentity::missing("trustfmt"),
                cargo_formatter: BoundToolIdentity::missing("targo-fmt"),
                tippy: BoundToolIdentity::missing("tippy"),
                targo_tippy: BoundToolIdentity::missing("targo-tippy"),
                tippy_driver: BoundToolIdentity::missing("tippy-driver"),
                analyzer: BoundToolIdentity::missing("trust-analyzer"),
                daemon: BoundToolIdentity::missing("trustd"),
                miri: BoundToolIdentity::missing("trust-miri"),
                targo_miri: BoundToolIdentity::missing("targo-miri"),
            },
            stage0: Some(Stage0Info {
                source: "bootstrap/trust-stage0".to_string(),
                channel_manifest_sha256: Some("d".repeat(64)),
            }),
        }
    }

    #[test]
    fn parses_flat_version_source() {
        let source = parse_version_source(&source_text("0.1.0")).unwrap();
        assert_eq!(source.trust_product_version, "0.1.0");
        assert_eq!(source.schemas["verifier_api"], "trust.verifier-api.v1");
    }

    #[test]
    fn rejects_invalid_product_version_without_checking_rust_version() {
        let err = parse_version_source(&source_text("1.2")).unwrap_err();
        assert!(matches!(err, VersionError::InvalidProductVersion { .. }));
    }

    #[test]
    fn rejects_unknown_rust_alignment_revision() {
        let text = source_text("0.1.0").replace(
            "revision = \"rust-lang/rust:5e91de65d75d3c849c643f5079509b9e5985a5c0\"",
            "revision = \"unknown\"",
        );
        let err = parse_version_source(&text).unwrap_err();
        assert!(matches!(err, VersionError::InvalidRustAlignment { field: "revision", .. }));
    }

    #[test]
    fn rejects_stale_registered_version_schema() {
        let text = source_text("0.1.0")
            .replace("version = \"trust.version.v3\"", "version = \"trust.version.v2\"");
        let err = parse_version_source(&text).unwrap_err();
        assert!(matches!(err, VersionError::InvalidRegisteredVersionSchema { .. }));
    }

    #[test]
    fn renders_json_with_separate_tool_identities() {
        let source = parse_version_source(&source_text("0.1.0")).unwrap();
        let identity = TrustVersionIdentity::from_source_and_runtime(source, runtime());
        let value: serde_json::Value =
            serde_json::from_str(&identity.render_json_pretty().unwrap()).unwrap();

        assert_eq!(value["schema_version"], VERSION_SCHEMA);
        assert_eq!(value["trust_product_version"], "0.1.0");
        assert_eq!(value["rust_compat_version"], "1.96.0-dev");
        assert_eq!(value["tools"]["frontend"]["name"], "targo");
        assert_eq!(value["tools"]["extension"]["name"], "targo-trust");
        assert_eq!(value["tools"]["compiler"]["name"], "trustc");
        assert_eq!(value["tools"]["documentation"]["name"], "trustdoc");
        assert_eq!(value["tools"]["formatter"]["name"], "trustfmt");
        assert_eq!(value["tools"]["cargo_formatter"]["name"], "targo-fmt");
        assert_eq!(value["tools"]["tippy"]["name"], "tippy");
        assert_eq!(value["tools"]["targo_tippy"]["name"], "targo-tippy");
        assert_eq!(value["tools"]["tippy_driver"]["name"], "tippy-driver");
        assert_eq!(value["tools"]["analyzer"]["name"], "trust-analyzer");
        assert_eq!(value["tools"]["daemon"]["name"], "trustd");
        assert_eq!(value["tools"]["miri"]["name"], "trust-miri");
        assert_eq!(value["tools"]["targo_miri"]["name"], "targo-miri");
        assert_eq!(value["schemas"]["verifier_api"], "trust.verifier-api.v1");
    }

    #[test]
    fn reads_legacy_clippy_tool_keys_but_serializes_only_tippy_keys() {
        let tools = runtime().tools;
        let mut legacy = serde_json::to_value(&tools).unwrap();
        let object = legacy.as_object_mut().unwrap();
        object.remove("daemon").unwrap();
        object.remove("tippy").unwrap();
        object.remove("targo_tippy").unwrap();
        object.remove("tippy_driver").unwrap();
        object.insert(
            "clippy".to_string(),
            serde_json::to_value(BoundToolIdentity::missing("targo-clippy")).unwrap(),
        );
        object.insert(
            "clippy_driver".to_string(),
            serde_json::to_value(BoundToolIdentity::missing("trust-clippy-driver")).unwrap(),
        );

        let parsed: BoundTools = serde_json::from_value(legacy).unwrap();
        assert_eq!(parsed.tippy.name, "tippy");
        assert_eq!(parsed.tippy.resolution.as_deref(), Some("not-found"));
        assert_eq!(parsed.targo_tippy.name, "targo-clippy");
        assert_eq!(parsed.tippy_driver.name, "trust-clippy-driver");
        assert_eq!(parsed.daemon, BoundToolIdentity::missing("trustd"));

        let canonical = serde_json::to_value(parsed).unwrap();
        assert!(canonical["tippy"].is_object());
        assert!(canonical["targo_tippy"].is_object());
        assert!(canonical["tippy_driver"].is_object());
        assert_eq!(canonical["daemon"]["name"], "trustd");
        assert!(canonical.get("clippy").is_none());
        assert!(canonical.get("clippy_driver").is_none());
    }

    #[test]
    fn superseded_identity_schemas_are_rejected_not_migrated() {
        // Trust used to silently accept `trust.version.v1` payloads and rewrite
        // them to the current schema on read. That bridge is burned: an old
        // payload is old evidence, and evidence is not something to upgrade
        // behind the reader's back. Regenerate it instead.
        let source = parse_version_source(&source_text("0.1.0")).unwrap();
        let identity = TrustVersionIdentity::from_source_and_runtime(source, runtime());
        for superseded in ["trust.version.v1", "trust.version.v2"] {
            let mut old = serde_json::to_value(&identity).unwrap();
            old["schema_version"] = superseded.into();
            assert!(
                serde_json::from_value::<TrustVersionIdentity>(old).is_err(),
                "{superseded} must be rejected, not migrated"
            );
        }
    }

    #[test]
    fn rejects_unknown_or_internally_inconsistent_identity_schemas() {
        let source = parse_version_source(&source_text("0.1.0")).unwrap();
        let identity = TrustVersionIdentity::from_source_and_runtime(source, runtime());
        let mut future = serde_json::to_value(&identity).unwrap();
        future["schema_version"] = "trust.version.v999".into();
        assert!(serde_json::from_value::<TrustVersionIdentity>(future).is_err());

        let mut inconsistent = serde_json::to_value(identity).unwrap();
        inconsistent["schemas"]["version"] = "trust.version.v999".into();
        assert!(serde_json::from_value::<TrustVersionIdentity>(inconsistent).is_err());
    }

    #[test]
    fn records_rejected_inherited_rust_named_tool_without_binding_path() {
        let rejected =
            BoundToolIdentity::rejected_inherited("trustfmt", "rustfmt", "stage2/bin/rustfmt");

        assert_eq!(rejected.name, "trustfmt");
        assert!(!rejected.has_bound_path());
        assert!(rejected.has_forbidden_inherited_evidence());
        assert_eq!(rejected.rejected_inherited_name.as_deref(), Some("rustfmt"));
        assert_eq!(rejected.rejected_path.as_deref(), Some("stage2/bin/rustfmt"));
    }

    #[test]
    fn text_output_names_trust_and_compatibility() {
        let source = parse_version_source(&source_text("0.1.0")).unwrap();
        let text = TrustVersionIdentity::from_source_and_runtime(source, runtime()).render_text();

        assert!(text.contains("Trust 0.1.0"));
        assert!(text.contains("rust-compat: 1.96.0-dev"));
        assert!(text.contains("targo: targo 1.96.0-dev"));
        assert!(text.contains("targo-trust: targo-trust 0.1.0"));
        assert!(text.contains("trustc: trustc 1.96.0-dev"));
        assert!(text.contains("trustdoc: trustdoc [not-found]"));
        assert!(text.contains("trustfmt: trustfmt [not-found]"));
        assert!(text.contains("targo-fmt: targo-fmt [not-found]"));
        assert!(text.contains("tippy: tippy [not-found]"));
        assert!(text.contains("targo-tippy: targo-tippy [not-found]"));
        assert!(text.contains("tippy-driver: tippy-driver [not-found]"));
        assert!(text.contains("trust-analyzer: trust-analyzer [not-found]"));
        assert!(text.contains("trustd: trustd [not-found]"));
        assert!(text.contains("trust-miri: trust-miri [not-found]"));
        assert!(text.contains("targo-miri: targo-miri [not-found]"));
    }
}
