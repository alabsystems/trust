//! `stage0-metadata-coherence-smoke` — validate the committed stage0 metadata.
//!
//! This is deliberately **not** the canonical `stage0-lineage` proof: the
//! materialized `*.tar.xz` payloads and authenticated producer attestations are
//! absent in a dev checkout, so co-committed names and hashes cannot establish
//! payload provenance. The canonical mode remains registered-but-blocked. This
//! diagnostic checks that the metadata which is present is internally exact.
//! It reads the three tracked lineage sources —
//!
//!   * `src/stage0` (the bootstrap pin file: channel, hashes, commit, payloads),
//!   * `bootstrap/trust-stage0/dist/channel-rust-trust.toml` (+ its `.sha256`
//!     pins) (the dist channel manifest the default bootstrap consumes),
//!   * `bootstrap/trust-stage0/trust-stage0-admission.json` (the payload-root
//!     admission record),
//!
//! — and inventories the consistency and disclosed gaps among them:
//!
//! 1. The channel manifest's byte digest triangulates: the recomputed sha256
//!    equals the beside-manifest `.sha256` pin, the dated-snapshot `.sha256`
//!    pin, `src/stage0`'s `compiler_channel_manifest_hash` /
//!    `rustfmt_channel_manifest_hash`, and the admission record's
//!    `manifest_hash`. A tamper on any copy breaks the gate.
//! 2. Trust-rooted, no stock dependency: `compiler_dist_channel` /
//!    `rustfmt_dist_channel` are `trust`; the compiler/rustfmt versions carry
//!    the owned `-trust` channel token; every distribution URL in `src/stage0`
//!    and the manifest is a `file://` seed-relative URL (never an
//!    `http(s)://` / `rust-lang.org` stock-distribution URL); every pinned
//!    payload leaf is a Trust-branded artifact, never a stock stage0 leaf
//!    (`rustc-*`, `cargo-*`, `rust-std-*`, `rustfmt-*`, `clippy-*`, …).
//! 3. The payload pin sets triangulate: `src/stage0`'s `dist/<date>/<leaf>`
//!    pins are exactly the admission record's payloads (equal paths + digests),
//!    and each is backed by a same-digest available payload in the manifest.
//! 4. The `src/stage0` and admission seed commit agree. The manifest's embedded
//!    compiler commit is validated and reported separately; it currently
//!    differs, and this smoke does not relabel either identifier as authenticated
//!    payload-producer provenance.
//!
//! Every inconsistency, missing source, or stock-Rust reference bails with a
//! precise reason. `policy.strict` /`release` additionally require the metadata
//! inventory to name a *complete* self-hosting
//! seed (the core `trustc`/`targo`/`trust-std` payloads must be pinned), so a
//! metadata-only stub cannot satisfy even this smoke. Canonical release
//! evidence remains blocked regardless of the smoke result.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use anyhow::{Context, Result, bail};
use serde_json::Value;

use super::{GatePolicy, read_bounded_exact_file_under, section};

const OWNED_CHANNEL: &str = "trust";
const ADMISSION_SCHEMA: &str = "trust.stage0-payload-root-admission.v1";

const MAX_STAGE0_BYTES: u64 = 1024 * 1024;
const MAX_MANIFEST_BYTES: u64 = 16 * 1024 * 1024;
const MAX_ADMISSION_BYTES: u64 = 1024 * 1024;
const MAX_SHA256_FILE_BYTES: u64 = 4 * 1024;

const SEED_DIR: &str = "bootstrap/trust-stage0";

/// Stock stage0 component leaf prefixes. A Trust seed renames every one of
/// these to an owned spelling (`trustc-*`, `trust-std-*`, `trustfmt-*`,
/// `targo-*`, `tippy-*`, …), so a payload leaf beginning with any of these is
/// a stock-Rust dependency leaking into the seed. Prefix (not substring)
/// matching is deliberate: `trustc-` must not trip the `rustc-` rule.
const STOCK_STAGE0_LEAF_PREFIXES: &[&str] = &[
    "rustc-",
    "cargo-",
    "cargo-clippy-",
    "clippy-",
    "rust-std-",
    "rust-src-",
    "rust-docs-",
    "rust-docs-json-",
    "rust-analysis-",
    "rust-analyzer-",
    "rustfmt-",
    "miri-",
    "llvm-tools-",
    "rust-mingw-",
    "rust-demangler-",
];

/// Core payloads a *complete* self-hosting Trust seed must pin (matched by leaf
/// prefix). Required only under `policy.strict`/`release`.
const REQUIRED_SELF_HOST_LEAF_PREFIXES: &[&str] = &["trustc-", "targo-", "trust-std-"];

pub(super) fn run(root: &Path, policy: GatePolicy) -> Result<()> {
    section("Stage0 metadata coherence smoke (non-authoritative)");
    println!(
        "Scope: checks committed src/stage0 + manifest + admission metadata only. This does not prove payload provenance or satisfy canonical stage0-lineage."
    );

    // 1. src/stage0 — the bootstrap pin file.
    let stage0 = load_stage0(root)?;
    println!(
        "Parsed src/stage0: {} config keys, {} payload pins",
        stage0.config.len(),
        stage0.pins.len()
    );

    // Trust-rooted channel + version (rejects stock nightly/beta/stable/dev).
    let compiler_channel = stage0.require("compiler_dist_channel")?;
    let rustfmt_channel = stage0.require("rustfmt_dist_channel")?;
    if compiler_channel != OWNED_CHANNEL {
        bail!(
            "src/stage0 compiler_dist_channel must be the owned `{OWNED_CHANNEL}` channel, got `{compiler_channel}` (a stock-Rust channel is not a Trust seed)"
        );
    }
    if rustfmt_channel != OWNED_CHANNEL {
        bail!(
            "src/stage0 rustfmt_dist_channel must be the owned `{OWNED_CHANNEL}` channel, got `{rustfmt_channel}`"
        );
    }
    for key in ["compiler_version", "rustfmt_version"] {
        let version = stage0.require(key)?;
        if !version_carries_owned_channel(version) {
            bail!(
                "src/stage0 {key} `{version}` does not carry the owned `-{OWNED_CHANNEL}` channel token; the seed toolchain must be Trust-branded, not stock Rust"
            );
        }
    }

    // Trust-rooted distribution servers (no stock http(s)/rust-lang.org URLs).
    // Validate the required roots plus every future URL/server-shaped key and
    // every value carrying a URI scheme, so adding a new network authority
    // cannot bypass a hard-coded key list.
    for key in ["dist_server", "artifacts_server", "artifacts_with_llvm_assertions_server"] {
        stage0.require(key)?;
    }
    for (key, value) in &stage0.config {
        if is_network_key(key) || value.contains("://") {
            validate_seed_url(value, &format!("src/stage0 {key}"))?;
        }
    }

    // Commit + date must be internally consistent within src/stage0.
    let seed_commit = stage0.require("compiler_git_commit_hash")?;
    require_hex(seed_commit, 40, "src/stage0 compiler_git_commit_hash")?;
    if stage0.require("rustfmt_git_commit_hash")? != seed_commit {
        bail!("src/stage0 compiler_git_commit_hash and rustfmt_git_commit_hash disagree");
    }
    let date = stage0.require("compiler_date")?.to_string();
    if !is_simple_date(&date) {
        bail!("src/stage0 compiler_date is not a canonical YYYY-MM-DD date: {date}");
    }
    if stage0.require("rustfmt_date")? != date {
        bail!("src/stage0 compiler_date and rustfmt_date disagree");
    }

    let manifest_hash = stage0.require("compiler_channel_manifest_hash")?.to_string();
    require_hex(&manifest_hash, 64, "src/stage0 compiler_channel_manifest_hash")?;
    if stage0.require("rustfmt_channel_manifest_hash")? != manifest_hash {
        bail!(
            "src/stage0 compiler_channel_manifest_hash and rustfmt_channel_manifest_hash disagree; the seed does not pin a single channel manifest"
        );
    }

    // 2. The channel manifest + its digest triangulation.
    let manifest_rel = format!("{SEED_DIR}/dist/channel-rust-{OWNED_CHANNEL}.toml");
    let manifest_bytes =
        read_bounded_exact_file_under(root, Path::new(&manifest_rel), MAX_MANIFEST_BYTES)
            .with_context(|| format!("missing committed channel manifest {manifest_rel}"))?;
    let computed_manifest_hash = trust_types::digest::stable_sha256_hex(&manifest_bytes);
    println!("Channel manifest {manifest_rel}: sha256:{computed_manifest_hash}");

    if computed_manifest_hash != manifest_hash {
        bail!(
            "channel manifest digest does not match src/stage0 pin: computed {computed_manifest_hash}, src/stage0 pins {manifest_hash}; the committed manifest and its stage0 pin are out of sync"
        );
    }

    // Beside-manifest .sha256 pin.
    let beside_pin = read_bare_sha256(root, &format!("{manifest_rel}.sha256"))
        .context("missing or malformed beside-manifest channel-rust-trust.toml.sha256 pin")?;
    if beside_pin != computed_manifest_hash {
        bail!(
            "beside-manifest .sha256 pin {beside_pin} does not match the manifest digest {computed_manifest_hash}"
        );
    }

    // Dated-snapshot .sha256 pin (ties the manifest to the seed date).
    let dated_pin_rel = format!("{SEED_DIR}/dist/{date}/channel-rust-{OWNED_CHANNEL}.toml.sha256");
    let dated_pin = read_bare_sha256(root, &dated_pin_rel)
        .with_context(|| format!("missing or malformed dated-snapshot pin {dated_pin_rel}"))?;
    if dated_pin != computed_manifest_hash {
        bail!(
            "dated-snapshot pin {dated_pin_rel} = {dated_pin} does not match the manifest digest {computed_manifest_hash}"
        );
    }

    // Parse the manifest and validate every URL is a Trust-rooted file:// seed
    // URL, collecting the available payload (leaf -> digest) inventory.
    let manifest_text = String::from_utf8(manifest_bytes)
        .with_context(|| format!("{manifest_rel} is not valid UTF-8"))?;
    let manifest: toml::Value =
        manifest_text.parse().with_context(|| format!("failed to parse {manifest_rel}"))?;
    if manifest.get("manifest-version").and_then(toml::Value::as_str) != Some("2") {
        bail!("{manifest_rel} must carry manifest-version = \"2\"");
    }
    let manifest_date = manifest
        .get("date")
        .and_then(toml::Value::as_str)
        .with_context(|| format!("{manifest_rel} is missing top-level date"))?;
    if manifest_date != date {
        bail!(
            "channel manifest date {manifest_date} does not match src/stage0 compiler_date {date}"
        );
    }
    let mut manifest_payloads: BTreeMap<String, String> = BTreeMap::new();
    let mut manifest_commits: BTreeSet<String> = BTreeSet::new();
    let mut errors: Vec<String> = Vec::new();
    let Some(manifest_table) = manifest.as_table() else {
        bail!("{manifest_rel} is not a TOML table");
    };
    scan_manifest_table(
        manifest_table,
        "manifest",
        &mut manifest_payloads,
        &mut manifest_commits,
        &mut errors,
    );
    if !errors.is_empty() {
        for error in &errors {
            eprintln!("FAIL: {error}");
        }
        bail!(
            "channel manifest carries {} non-Trust-rooted or malformed distribution reference(s)",
            errors.len()
        );
    }
    if manifest_commits.len() != 1 {
        bail!(
            "channel manifest must carry exactly one embedded compiler commit, got {manifest_commits:?}"
        );
    }
    let manifest_commit = manifest_commits.iter().next().expect("one commit");
    println!(
        "Manifest declares {} available Trust-branded payload(s), all file:// seed-rooted",
        manifest_payloads.len()
    );

    // 3. src/stage0 payload pins — well-formed, Trust-branded, seed-dated.
    if stage0.pins.is_empty() {
        bail!("src/stage0 declares no payload pins; the committed seed has no lineage to prove");
    }
    let mut stage0_leaf_pins: BTreeMap<String, String> = BTreeMap::new();
    for (rel, hash) in &stage0.pins {
        let (pin_date, leaf) = split_pin_path(rel)
            .with_context(|| format!("src/stage0 payload pin is not dist/<date>/<leaf>: {rel}"))?;
        if pin_date != date {
            bail!(
                "src/stage0 payload pin {rel} is dated {pin_date} but the seed date is {date}; the pin set is not from one snapshot"
            );
        }
        require_hex(hash, 64, &format!("src/stage0 payload pin digest for {rel}"))?;
        validate_payload_leaf(leaf)?;
        if stage0_leaf_pins.insert(leaf.to_string(), hash.clone()).is_some() {
            bail!("src/stage0 pins the payload leaf {leaf} more than once");
        }
        // Each pin must be backed by a same-digest available manifest payload.
        match manifest_payloads.get(leaf) {
            None => bail!(
                "src/stage0 pins payload {leaf} but the channel manifest declares no available payload for it"
            ),
            Some(manifest_hash) if manifest_hash != hash => bail!(
                "digest mismatch for payload {leaf}: src/stage0 pins {hash}, manifest declares {manifest_hash}"
            ),
            Some(_) => {}
        }
    }

    // 4. Admission record — Trust-owned, matching commit/date/manifest, and its
    //    payload set is exactly the src/stage0 pin set.
    let admission_rel = format!("{SEED_DIR}/trust-stage0-admission.json");
    let admission_bytes =
        read_bounded_exact_file_under(root, Path::new(&admission_rel), MAX_ADMISSION_BYTES)
            .with_context(|| format!("missing committed admission record {admission_rel}"))?;
    let admission: Value = serde_json::from_slice(&admission_bytes)
        .with_context(|| format!("failed to parse {admission_rel}"))?;
    require_closed_admission_schema(&admission, &admission_rel)?;
    let mut admission_network_errors = Vec::new();
    scan_json_network_values(&admission, "admission", false, &mut admission_network_errors);
    if !admission_network_errors.is_empty() {
        bail!(
            "admission metadata carries invalid network authority: {}",
            admission_network_errors.join("; ")
        );
    }

    require_json_str(&admission, "schema", ADMISSION_SCHEMA, &admission_rel)?;
    require_json_str(&admission, "admission", "internal", &admission_rel)?;
    require_json_str(&admission, "dist_payload_mode", "full", &admission_rel)?;
    require_json_str(&admission, "promotion_decision", "admit-internal", &admission_rel)?;
    require_json_str(&admission, "owned_channel", OWNED_CHANNEL, &admission_rel)?;
    require_json_str(&admission, "source_channel", OWNED_CHANNEL, &admission_rel)?;
    match admission.get("public_upload") {
        Some(Value::Bool(false)) => {}
        _ => bail!(
            "{admission_rel} public_upload must be the literal boolean false; a Trust seed is never publicly uploaded"
        ),
    }
    let admission_seed_commit = admission
        .get("git_commit_hash")
        .and_then(Value::as_str)
        .with_context(|| format!("{admission_rel} is missing git_commit_hash"))?;
    if admission_seed_commit != seed_commit {
        bail!(
            "admission git_commit_hash {admission_seed_commit} does not match src/stage0 seed commit {seed_commit}"
        );
    }
    let admission_date = admission
        .get("date")
        .and_then(Value::as_str)
        .with_context(|| format!("{admission_rel} is missing date"))?;
    if admission_date != date {
        bail!("admission date {admission_date} does not match src/stage0 compiler_date {date}");
    }
    let admission_manifest_hash = admission
        .get("manifest_hash")
        .and_then(Value::as_str)
        .with_context(|| format!("{admission_rel} is missing manifest_hash"))?;
    if admission_manifest_hash != computed_manifest_hash {
        bail!(
            "admission manifest_hash {admission_manifest_hash} does not match the channel manifest digest {computed_manifest_hash}"
        );
    }

    let admission_payloads = parse_admission_payloads(&admission, &admission_rel)?;
    // Exact bijection between src/stage0 pins and admission payloads (same
    // relative paths, same digests).
    if admission_payloads != stage0.pins {
        let only_stage0: Vec<&String> =
            stage0.pins.keys().filter(|k| !admission_payloads.contains_key(*k)).collect();
        let only_admission: Vec<&String> =
            admission_payloads.keys().filter(|k| !stage0.pins.contains_key(*k)).collect();
        let digest_conflicts: Vec<String> = stage0
            .pins
            .iter()
            .filter_map(|(path, hash)| {
                admission_payloads.get(path).filter(|admission_hash| *admission_hash != hash).map(
                    |admission_hash| format!("{path}: stage0 {hash} vs admission {admission_hash}"),
                )
            })
            .collect();
        bail!(
            "admission payload set does not match the src/stage0 pin set: only-in-stage0={only_stage0:?}, only-in-admission={only_admission:?}, digest-conflicts={digest_conflicts:?}"
        );
    }

    println!(
        "Metadata inventory: manifest digest sha256:{computed_manifest_hash}; src/stage0 + admission seed commit {seed_commit}; manifest embedded compiler commit {manifest_commit}; date {date}; {} named payload pins consistent across all three metadata sources.",
        stage0.pins.len()
    );

    if manifest_commit != seed_commit {
        println!(
            "DISCLOSED GAP: seed metadata commit and manifest embedded compiler commit differ; this smoke does not infer which commit produced payload bytes."
        );
    }

    // policy: a release/strict seed must be a complete self-hosting seed.
    if policy.strict || policy.release {
        let missing: Vec<&str> = REQUIRED_SELF_HOST_LEAF_PREFIXES
            .iter()
            .copied()
            .filter(|prefix| !stage0_leaf_pins.keys().any(|leaf| leaf.starts_with(prefix)))
            .collect();
        if !missing.is_empty() {
            bail!(
                "strict/release stage0-lineage gate requires a complete self-hosting Trust seed; missing pinned payloads with leaf prefixes: {}",
                missing.join(", ")
            );
        }
        println!(
            "Strict/release: seed pins the core self-hosting payloads (trustc, targo, trust-std)."
        );
    }

    println!(
        "SMOKE PASS (non-authoritative): this metadata check cannot authenticate an ignored Stage2 receipt or its verifier runtime; canonical stage0-lineage remains blocked."
    );
    println!(
        "DISCLOSED GAP: archive bytes are unavailable, so this metadata smoke cannot confirm producer-side stripping of stock/retired secondary entrypoints (rustdoc, rustfmt, cargo-fmt, cargo-trust, rust-analyzer, cargo-clippy, clippy-driver, targo-clippy, trust-clippy, trust-clippy-driver, and rust-analyzer-proc-macro-srv)."
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// src/stage0 parsing
// ---------------------------------------------------------------------------

struct Stage0 {
    /// Plain `key=value` config entries (channel, hashes, commit, date, …).
    config: BTreeMap<String, String>,
    /// Payload pins keyed by `dist/<date>/<leaf>` relative path -> sha256.
    pins: BTreeMap<String, String>,
}

impl Stage0 {
    fn require(&self, key: &str) -> Result<&str> {
        self.config
            .get(key)
            .map(String::as_str)
            .filter(|value| !value.is_empty())
            .with_context(|| format!("src/stage0 is missing required key `{key}`"))
    }
}

fn load_stage0(root: &Path) -> Result<Stage0> {
    let bytes = read_bounded_exact_file_under(root, Path::new("src/stage0"), MAX_STAGE0_BYTES)
        .context("missing committed src/stage0 bootstrap pin file")?;
    let text = String::from_utf8(bytes).context("src/stage0 is not valid UTF-8")?;
    parse_stage0(&text)
}

fn parse_stage0(text: &str) -> Result<Stage0> {
    let mut config = BTreeMap::new();
    let mut pins = BTreeMap::new();
    for raw in text.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (key, value) = line
            .split_once('=')
            .with_context(|| format!("src/stage0 line is not key=value: {line}"))?;
        let key = key.trim();
        let value = value.trim();
        if key.is_empty() {
            bail!("src/stage0 line has an empty key: {line}");
        }
        if key.starts_with("dist/") {
            if pins.insert(key.to_string(), value.to_string()).is_some() {
                bail!("src/stage0 pins {key} more than once");
            }
        } else if config.insert(key.to_string(), value.to_string()).is_some() {
            bail!("src/stage0 sets config key {key} more than once");
        }
    }
    Ok(Stage0 { config, pins })
}

// ---------------------------------------------------------------------------
// Manifest scanning
// ---------------------------------------------------------------------------

/// Recursively validate every `*_url` string in the manifest is a Trust-rooted
/// `file://` seed URL, and record each available (`xz`/`gz`) payload as
/// leaf -> digest. Findings accumulate into `errors`.
fn scan_manifest_table(
    table: &toml::map::Map<String, toml::Value>,
    context: &str,
    payloads: &mut BTreeMap<String, String>,
    commits: &mut BTreeSet<String>,
    errors: &mut Vec<String>,
) {
    for (key, value) in table {
        let item_context = format!("{context}.{key}");
        let network_key = is_network_key(key);
        if network_key && !matches!(value, toml::Value::String(_)) {
            errors.push(format!("{item_context} is a URL/server key but is not a string"));
        }
        match value {
            toml::Value::Table(inner) => {
                scan_manifest_table(inner, &item_context, payloads, commits, errors)
            }
            toml::Value::Array(items) => {
                for (index, item) in items.iter().enumerate() {
                    if let Some(inner) = item.as_table() {
                        scan_manifest_table(
                            inner,
                            &format!("{item_context}[{index}]"),
                            payloads,
                            commits,
                            errors,
                        );
                    } else if let Some(text) = item.as_str() {
                        if text.contains("://") {
                            if let Err(error) = validate_seed_url(text, &item_context) {
                                errors.push(error.to_string());
                            }
                        }
                    }
                }
            }
            toml::Value::String(commit) if key == "git_commit_hash" => {
                if let Err(error) = require_hex(commit, 40, &item_context) {
                    errors.push(error.to_string());
                } else {
                    commits.insert(commit.clone());
                }
            }
            toml::Value::String(url) if is_network_key(key) || url.contains("://") => {
                if let Err(error) = validate_seed_url(url, &item_context) {
                    errors.push(error.to_string());
                    continue;
                }
                if key == "xz_url" || key == "gz_url" {
                    let leaf = match url.rsplit('/').next().filter(|leaf| !leaf.is_empty()) {
                        Some(leaf) => leaf,
                        None => {
                            errors
                                .push(format!("channel manifest {key} has no payload leaf: {url}"));
                            continue;
                        }
                    };
                    if let Err(error) = validate_payload_leaf(leaf) {
                        errors.push(error.to_string());
                        continue;
                    }
                    let hash_key = if key == "xz_url" { "xz_hash" } else { "gz_hash" };
                    match table.get(hash_key).and_then(toml::Value::as_str) {
                        None => errors.push(format!(
                            "channel manifest payload {leaf} has {key} but no {hash_key}"
                        )),
                        Some(hash) => {
                            if let Err(error) = require_hex(
                                hash,
                                64,
                                &format!("channel manifest {hash_key} for {leaf}"),
                            ) {
                                errors.push(error.to_string());
                            } else if let Some(previous) =
                                payloads.insert(leaf.to_string(), hash.to_string())
                            {
                                if previous != *hash {
                                    errors.push(format!(
                                        "channel manifest declares conflicting digests for payload {leaf}"
                                    ));
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

fn scan_json_network_values(
    value: &Value,
    context: &str,
    network_key: bool,
    errors: &mut Vec<String>,
) {
    match value {
        Value::Object(object) => {
            if network_key {
                errors.push(format!("{context} is a URL/server key but is not a string"));
            }
            for (key, child) in object {
                scan_json_network_values(
                    child,
                    &format!("{context}.{key}"),
                    is_network_key(key),
                    errors,
                );
            }
        }
        Value::Array(items) => {
            if network_key {
                errors.push(format!("{context} is a URL/server key but is not a string"));
            }
            for (index, child) in items.iter().enumerate() {
                scan_json_network_values(child, &format!("{context}[{index}]"), false, errors);
            }
        }
        Value::String(text) if network_key || text.contains("://") => {
            if let Err(error) = validate_seed_url(text, context) {
                errors.push(error.to_string());
            }
        }
        _ if network_key => {
            errors.push(format!("{context} is a URL/server key but is not a string"));
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Admission parsing
// ---------------------------------------------------------------------------

fn require_closed_admission_schema(admission: &Value, source: &str) -> Result<()> {
    let object =
        admission.as_object().with_context(|| format!("{source} must be a JSON object"))?;
    let actual = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = [
        "admission",
        "date",
        "dist_payload_mode",
        "git_commit_hash",
        "manifest_hash",
        "owned_channel",
        "payloads",
        "promotion_decision",
        "public_upload",
        "schema",
        "source_channel",
    ]
    .into_iter()
    .collect::<BTreeSet<_>>();
    if actual != expected {
        let missing = expected.difference(&actual).copied().collect::<Vec<_>>();
        let unexpected = actual.difference(&expected).copied().collect::<Vec<_>>();
        bail!("{source} schema is not closed: missing={missing:?}, unexpected={unexpected:?}");
    }
    Ok(())
}

fn parse_admission_payloads(admission: &Value, source: &str) -> Result<BTreeMap<String, String>> {
    let items = admission
        .get("payloads")
        .and_then(Value::as_array)
        .with_context(|| format!("{source} is missing a payloads array"))?;
    if items.is_empty() {
        bail!("{source} declares no payloads");
    }
    let mut out = BTreeMap::new();
    for (index, item) in items.iter().enumerate() {
        let idx = index + 1;
        let item_object = item
            .as_object()
            .with_context(|| format!("{source} payloads[{idx}] must be an object"))?;
        let keys = item_object.keys().map(String::as_str).collect::<BTreeSet<_>>();
        if keys != BTreeSet::from(["relative_path", "sha256"]) {
            bail!(
                "{source} payloads[{idx}] schema must contain exactly relative_path and sha256, got {keys:?}"
            );
        }
        let relative_path = item
            .get("relative_path")
            .and_then(Value::as_str)
            .with_context(|| format!("{source} payloads[{idx}] is missing relative_path"))?;
        let sha256 = item
            .get("sha256")
            .and_then(Value::as_str)
            .with_context(|| format!("{source} payloads[{idx}] is missing sha256"))?;
        require_hex(sha256, 64, &format!("{source} payloads[{idx}] sha256"))?;
        let (_, leaf) = split_pin_path(relative_path).with_context(|| {
            format!(
                "{source} payloads[{idx}] relative_path is not dist/<date>/<leaf>: {relative_path}"
            )
        })?;
        validate_payload_leaf(leaf)?;
        if out.insert(relative_path.to_string(), sha256.to_string()).is_some() {
            bail!("{source} declares payload {relative_path} more than once");
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Shared validation helpers
// ---------------------------------------------------------------------------

fn is_network_key(key: &str) -> bool {
    matches!(key, "url" | "uri" | "server")
        || key.ends_with("_url")
        || key.ends_with("_uri")
        || key.ends_with("_server")
}

/// A distribution URL that keeps the seed self-contained: a `file://` URL that
/// points inside the repo-local Trust stage0 seed. Any `http(s)://` URL, any
/// `rust-lang.org` host, or any URL outside the seed directory is a stock-Rust
/// distribution dependency and is rejected.
fn validate_seed_url(url: &str, context: &str) -> Result<()> {
    let prefix = format!("file://{{trust-root}}/{SEED_DIR}");
    let Some(rest) = url.strip_prefix(&prefix) else {
        bail!("{context} must use the exact repo-placeholder seed root {prefix}, got: {url}");
    };
    if !rest.is_empty() && !rest.starts_with('/') {
        bail!("{context} escapes the exact seed-root boundary: {url}");
    }
    if url.chars().any(|ch| matches!(ch, '\\' | '?' | '#' | '%') || ch.is_control()) {
        bail!("{context} contains an encoded, escaped, or control-bearing seed path: {url}");
    }
    if !rest.is_empty() {
        for component in rest[1..].split('/') {
            if component.is_empty() || matches!(component, "." | "..") {
                bail!("{context} contains a non-canonical seed path component: {url}");
            }
        }
    }
    Ok(())
}

/// A pinned payload leaf must be a Trust-branded artifact carrying the owned
/// channel token, never a stock stage0 component leaf.
fn validate_payload_leaf(leaf: &str) -> Result<()> {
    if let Some(prefix) =
        STOCK_STAGE0_LEAF_PREFIXES.iter().find(|prefix| leaf.starts_with(**prefix))
    {
        bail!(
            "payload leaf `{leaf}` is a stock-Rust stage0 component (`{prefix}…`); a Trust seed must pin only owned artifacts"
        );
    }
    if !leaf.contains(&format!("-{OWNED_CHANNEL}-"))
        && !leaf.contains(&format!("-{OWNED_CHANNEL}."))
    {
        bail!(
            "payload leaf `{leaf}` does not carry the owned `-{OWNED_CHANNEL}` channel token; it is not a Trust seed artifact"
        );
    }
    Ok(())
}

/// A compiler/rustfmt version string on the owned channel (e.g. `1.96.0-trust`
/// or `1.96.0-trust (…)`): the leading version core must end in `-trust`.
fn version_carries_owned_channel(version: &str) -> bool {
    let token = format!("-{OWNED_CHANNEL}");
    version.split(|c: char| c == ' ' || c == '\t').next().is_some_and(|core| core.ends_with(&token))
}

/// Split `dist/<date>/<leaf>` into (date, leaf). Rejects any other shape.
fn split_pin_path(relative: &str) -> Result<(&str, &str)> {
    let mut parts = relative.split('/');
    match (parts.next(), parts.next(), parts.next(), parts.next()) {
        (Some("dist"), Some(date), Some(leaf), None) if !date.is_empty() && !leaf.is_empty() => {
            Ok((date, leaf))
        }
        _ => bail!("payload path is not dist/<date>/<leaf>: {relative}"),
    }
}

fn require_hex(value: &str, len: usize, context: &str) -> Result<()> {
    if value.len() != len
        || !value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        bail!("{context} must be a canonical lowercase {len}-hex digest: {value}");
    }
    Ok(())
}

fn is_simple_date(value: &str) -> bool {
    let bytes = value.as_bytes();
    if bytes.len() != 10
        || bytes[4] != b'-'
        || bytes[7] != b'-'
        || !value[..4].bytes().all(|b| b.is_ascii_digit())
        || !value[5..7].bytes().all(|b| b.is_ascii_digit())
        || !value[8..].bytes().all(|b| b.is_ascii_digit())
    {
        return false;
    }
    let year: u32 = value[..4].parse().unwrap_or(0);
    let month: u32 = value[5..7].parse().unwrap_or(0);
    let day: u32 = value[8..].parse().unwrap_or(0);
    if year == 0 || !(1..=12).contains(&month) || day == 0 {
        return false;
    }
    let max_day = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) => 29,
        2 => 28,
        _ => return false,
    };
    day <= max_day
}

/// Read a bare-sha256 pin file (`<hash>` optionally followed by whitespace and
/// a filename) and return the validated 64-hex digest.
fn read_bare_sha256(root: &Path, relative: &str) -> Result<String> {
    let bytes = read_bounded_exact_file_under(root, Path::new(relative), MAX_SHA256_FILE_BYTES)
        .with_context(|| format!("missing sha256 pin {relative}"))?;
    let text =
        String::from_utf8(bytes).with_context(|| format!("{relative} is not valid UTF-8"))?;
    let token = text.split_whitespace().next().with_context(|| format!("{relative} is empty"))?;
    require_hex(token, 64, relative)?;
    Ok(token.to_string())
}

fn require_json_str(value: &Value, field: &str, expected: &str, source: &str) -> Result<()> {
    let actual = value
        .get(field)
        .and_then(Value::as_str)
        .with_context(|| format!("{source} is missing string field `{field}`"))?;
    if actual != expected {
        bail!("{source} {field} must be `{expected}`, got `{actual}`");
    }
    Ok(())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stock_leaves_are_rejected_trust_leaves_accepted() {
        // Owned Trust leaves — accepted (owned channel token, no stock prefix).
        for leaf in [
            "targo-1.96.0-trust-aarch64-apple-darwin.tar.xz",
            "trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz",
            "trustc-dev-1.96.0-trust-aarch64-apple-darwin.tar.xz",
            "trust-std-1.96.0-trust-aarch64-apple-darwin.tar.xz",
            "trust-src-1.96.0-trust.tar.xz",
            "trustfmt-1.96.0-trust-aarch64-apple-darwin.tar.xz",
            "tippy-1.96.0-trust-aarch64-apple-darwin.tar.xz",
            "trust-analyzer-1.96.0-trust-aarch64-apple-darwin.tar.xz",
            "targo-trust-1.96.0-trust-aarch64-apple-darwin.tar.xz",
        ] {
            assert!(validate_payload_leaf(leaf).is_ok(), "should accept Trust leaf {leaf}");
        }
        // Stock stage0 leaves — rejected.
        for leaf in [
            "rustc-1.96.0-nightly-aarch64-apple-darwin.tar.xz",
            "cargo-1.96.0-nightly-aarch64-apple-darwin.tar.xz",
            "rust-std-1.96.0-nightly-aarch64-apple-darwin.tar.xz",
            "rustfmt-1.96.0-nightly-aarch64-apple-darwin.tar.xz",
            "clippy-1.96.0-nightly-aarch64-apple-darwin.tar.xz",
        ] {
            assert!(validate_payload_leaf(leaf).is_err(), "should reject stock leaf {leaf}");
        }
        // A Trust-prefixed leaf with no owned channel token is still rejected.
        assert!(validate_payload_leaf("trustc-1.96.0-nightly-aarch64.tar.xz").is_err());
    }

    #[test]
    fn seed_urls_reject_stock_and_network_hosts() {
        assert!(validate_seed_url(
            "file://{trust-root}/bootstrap/trust-stage0/dist/2026-07-06/trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz",
            "ctx"
        )
        .is_ok());
        assert!(validate_seed_url("file://{trust-root}/bootstrap/trust-stage0", "ctx").is_ok());
        for bad in [
            "https://static.rust-lang.org/dist/2026-07-06/rustc-nightly.tar.xz",
            "http://ci-artifacts.rust-lang.org/rustc.tar.xz",
            "https://forge.rust-lang.org/x",
            "file:///tmp/outside-the-seed/rustc.tar.xz",
            "file://{trust-root}/bootstrap/trust-stage0/../../outside/trustc-1-trust-x.tar.xz",
            "file://{trust-root}/bootstrap/trust-stage0/%2e%2e/outside/trustc-1-trust-x.tar.xz",
            "file://{trust-root}/bootstrap/trust-stage0x/trustc-1-trust-x.tar.xz",
        ] {
            assert!(validate_seed_url(bad, "ctx").is_err(), "should reject {bad}");
        }
    }

    #[test]
    fn version_owned_channel_detection() {
        assert!(version_carries_owned_channel("1.96.0-trust"));
        assert!(version_carries_owned_channel("1.96.0-trust (2b5880678 2026-07-06)"));
        assert!(!version_carries_owned_channel("1.96.0-nightly"));
        assert!(!version_carries_owned_channel("1.96.0"));
    }

    #[test]
    fn pin_paths_must_be_dist_date_leaf() {
        assert_eq!(
            split_pin_path("dist/2026-07-06/trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz")
                .unwrap(),
            ("2026-07-06", "trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz")
        );
        assert!(split_pin_path("dist/2026-07-06").is_err());
        assert!(split_pin_path("dist/2026-07-06/a/b").is_err());
        assert!(split_pin_path("other/2026-07-06/x").is_err());
    }

    #[test]
    fn hex_and_date_validation() {
        assert!(require_hex(&"a".repeat(64), 64, "ctx").is_ok());
        assert!(require_hex(&"A".repeat(64), 64, "ctx").is_err()); // uppercase
        assert!(require_hex(&"a".repeat(63), 64, "ctx").is_err()); // short
        assert!(require_hex("zz", 2, "ctx").is_err()); // non-hex
        assert!(is_simple_date("2026-07-06"));
        assert!(!is_simple_date("2026-7-06"));
        assert!(!is_simple_date("2026/07/06"));
        assert!(!is_simple_date("2026-02-29"));
        assert!(is_simple_date("2024-02-29"));
    }

    #[test]
    fn stage0_parsing_splits_config_and_pins() {
        let text = "\
# comment
compiler_dist_channel=trust
compiler_version=1.96.0-trust

dist/2026-07-06/trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz="
            .to_string()
            + &"a".repeat(64)
            + "\n";
        let stage0 = parse_stage0(&text).unwrap();
        assert_eq!(stage0.require("compiler_dist_channel").unwrap(), "trust");
        assert_eq!(stage0.pins.len(), 1);
        assert!(
            stage0
                .pins
                .contains_key("dist/2026-07-06/trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz")
        );
    }

    #[test]
    fn duplicate_stage0_keys_are_rejected() {
        assert!(parse_stage0("compiler_date=2026-07-06\ncompiler_date=2026-07-07\n").is_err());
    }

    #[test]
    fn manifest_scan_records_payloads_and_flags_stock_urls() {
        let manifest_text = format!(
            r#"
date = "2026-07-06"
[pkg.trustc.target.aarch64-apple-darwin]
available = true
xz_url = "file://{{trust-root}}/bootstrap/trust-stage0/dist/2026-07-06/trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz"
xz_hash = "{trust_hash}"
[pkg.rustc.target.x86_64-unknown-linux-gnu]
available = true
xz_url = "https://static.rust-lang.org/dist/2026-07-06/rustc-nightly.tar.xz"
xz_hash = "{stock_hash}"
"#,
            trust_hash = "a".repeat(64),
            stock_hash = "b".repeat(64),
        );
        let manifest: toml::Value = manifest_text.parse().unwrap();
        let mut payloads = BTreeMap::new();
        let mut errors = Vec::new();
        let mut commits = BTreeSet::new();
        scan_manifest_table(
            manifest.as_table().unwrap(),
            "manifest",
            &mut payloads,
            &mut commits,
            &mut errors,
        );
        assert!(payloads.contains_key("trustc-1.96.0-trust-aarch64-apple-darwin.tar.xz"));
        assert!(!errors.is_empty(), "stock rust-lang.org URL must be flagged");
    }

    #[test]
    fn manifest_scan_rejects_future_network_channels_and_non_string_url_keys() {
        let manifest: toml::Value = r#"
future_server = 7
future_uri = "https://example.invalid/uri"
mirrors = ["https://example.invalid/seed"]
"#
        .parse()
        .unwrap();
        let mut payloads = BTreeMap::new();
        let mut commits = BTreeSet::new();
        let mut errors = Vec::new();
        scan_manifest_table(
            manifest.as_table().unwrap(),
            "manifest",
            &mut payloads,
            &mut commits,
            &mut errors,
        );
        assert!(errors.iter().any(|error| error.contains("future_server")));
        assert!(errors.iter().any(|error| error.contains("future_uri")));
        assert!(errors.iter().any(|error| error.contains("example.invalid")));
    }

    #[test]
    fn admission_schema_rejects_undeclared_authority_fields() {
        let mut admission = serde_json::json!({
            "admission": "internal",
            "date": "2026-07-06",
            "dist_payload_mode": "full",
            "git_commit_hash": "a".repeat(40),
            "manifest_hash": "b".repeat(64),
            "owned_channel": "trust",
            "payloads": [],
            "promotion_decision": "admit-internal",
            "public_upload": false,
            "schema": ADMISSION_SCHEMA,
            "source_channel": "trust"
        });
        require_closed_admission_schema(&admission, "test").expect("canonical schema");
        admission
            .as_object_mut()
            .unwrap()
            .insert("producer_authenticated".into(), Value::Bool(true));
        assert!(require_closed_admission_schema(&admission, "test").is_err());
    }
}
