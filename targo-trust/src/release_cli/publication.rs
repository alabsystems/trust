use std::path::{Path, PathBuf};
use std::{fs, io};

use trust_release::{GateFinding, GateReport};

use crate::input_limits::{MAX_RELEASE_METADATA_BYTES, read_bounded_utf8_file};

use super::identity::{exact_file_sha256_with_prefix, file_sha256, read_trimmed};

pub(super) fn check_publication_inputs(root: &Path) -> GateReport {
    let mut findings = Vec::new();
    for relative in [
        "bootstrap/trust-stage0/dist/channel-rust-trust.toml",
        "bootstrap/trust-stage0/dist/channel-rust-trust.toml.sha256",
    ] {
        if !root.join(relative).is_file() {
            findings.push(GateFinding::error(
                "publication-input-missing",
                format!("missing publication input `{relative}`"),
            ));
        }
    }
    let manifest = root.join("bootstrap/trust-stage0/dist/channel-rust-trust.toml");
    let manifest_sha = root.join("bootstrap/trust-stage0/dist/channel-rust-trust.toml.sha256");
    if manifest.is_file() && manifest_sha.is_file() {
        let expected = read_trimmed(&manifest_sha)
            .and_then(|text| text.split_whitespace().next().map(str::to_string));
        let actual = file_sha256(&manifest);
        if expected.as_deref().is_none_or(|sha| actual.as_deref() != Some(sha)) {
            findings.push(GateFinding::error(
                "publication-channel-sha-mismatch",
                "channel-rust-trust.toml does not match channel-rust-trust.toml.sha256",
            ));
        }
    }

    GateReport::new("publication-inputs", findings).with_evidence_refs([
        "bootstrap/trust-stage0/dist/channel-rust-trust.toml",
        "bootstrap/trust-stage0/dist/channel-rust-trust.toml.sha256",
    ])
}

pub(super) fn check_publication_artifacts(root: &Path) -> GateReport {
    let dist_root = root.join("bootstrap/trust-stage0/dist");
    let channel_manifest = read_bounded_utf8_file(
        &dist_root.join("channel-rust-trust.toml"),
        MAX_RELEASE_METADATA_BYTES,
    )
    .ok()
    .and_then(|text| toml::from_str::<toml::Value>(&text).ok());
    let required = [
        ("trustc compiler package", "trustc-"),
        ("targo frontend package", "targo-"),
        ("targo-trust subcommand package", "targo-trust-"),
        ("std", "trust-std-"),
        ("source", "trust-src-"),
        ("docs", "trust-docs-"),
        ("trustfmt formatter package", "trustfmt-"),
        ("Tippy lint package", "tippy-"),
        ("trust-analyzer package", "trust-analyzer-"),
        ("LLVM tools", "llvm-tools-"),
    ];

    let mut findings = Vec::new();
    let mut evidence_refs = Vec::new();
    for (label, prefix) in required {
        let excludes = &[][..];
        match find_dist_artifact(&dist_root, prefix, excludes, channel_manifest.as_ref()) {
            Some(path) => evidence_refs.push(path.display().to_string()),
            None => findings.push(GateFinding::error(
                "publication-artifact-missing",
                format!(
                    "missing channel-manifest-bound publication artifact for {label} matching `{prefix}*`"
                ),
            )),
        }
    }

    GateReport::new("publication-artifacts", findings).with_evidence_refs(evidence_refs)
}

pub(super) fn check_publication_ledger(root: &Path, candidate_commit: Option<&str>) -> GateReport {
    // The ledger lives under bootstrap/trust-stage0/ (NOT release/): the
    // public-distribution cull gate forbids `release/publication-ledger.toml`
    // and any scan-location file whose name carries a `publication-ledger`
    // token, while this seed-publication record (0f2c5a43ce6, OFF_STOCK_RUST_PLAN
    // Phase 3) is a live release-CLI input. `bootstrap/trust-stage0/` is outside
    // the cull scan locations and `seed-ledger` carries no forbidden token, so
    // both subsystems' intents survive.
    let path = root.join("bootstrap/trust-stage0/seed-ledger.toml");
    let text = match read_bounded_utf8_file(&path, MAX_RELEASE_METADATA_BYTES) {
        Ok(text) => text,
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            return GateReport::new(
                "publication-ledger",
                vec![GateFinding::error(
                    "publication-ledger-missing",
                    "missing bootstrap/trust-stage0/seed-ledger.toml with tags, checksums, signatures, and promotion decision",
                )],
            );
        }
        Err(err) => {
            return GateReport::new(
                "publication-ledger",
                vec![GateFinding::error(
                    "publication-ledger-read",
                    format!("failed to read {}: {err}", path.display()),
                )],
            );
        }
    };

    let ledger: toml::Value = match toml::from_str(&text) {
        Ok(ledger) => ledger,
        Err(err) => {
            return GateReport::new(
                "publication-ledger",
                vec![GateFinding::error(
                    "publication-ledger-parse",
                    format!("failed to parse {}: {err}", path.display()),
                )],
            );
        }
    };

    let mut findings = Vec::new();
    let Some(table) = ledger.as_table() else {
        return GateReport::new(
            "publication-ledger",
            vec![GateFinding::error(
                "publication-ledger-schema",
                "publication ledger root must be a TOML table",
            )],
        )
        .with_evidence_refs([path.display().to_string()]);
    };
    const LEDGER_KEYS: &[&str] =
        &["candidate_commit", "tags", "checksums", "signatures", "promotion_decision"];
    for key in table.keys().filter(|key| !LEDGER_KEYS.contains(&key.as_str())) {
        findings.push(GateFinding::error(
            "publication-ledger-schema",
            format!("publication ledger contains unknown top-level field `{key}`"),
        ));
    }

    match (candidate_commit, table.get("candidate_commit").and_then(toml::Value::as_str)) {
        (Some(expected), Some(actual)) if actual == expected => {}
        (Some(expected), Some(_)) => findings.push(GateFinding::error(
            "publication-ledger-candidate-commit",
            format!("publication ledger does not bind candidate commit {expected}"),
        )),
        (Some(_), None) => findings.push(GateFinding::error(
            "publication-ledger-candidate-commit",
            "publication ledger is missing candidate_commit evidence",
        )),
        (None, _) => findings.push(GateFinding::error(
            "publication-ledger-candidate-commit",
            "publication ledger cannot be validated without candidate_commit",
        )),
    }

    for (code, description, key, kind) in [
        ("publication-ledger-tags", "release tags", "tags", LedgerValueKind::Tag),
        (
            "publication-ledger-checksums",
            "artifact checksums",
            "checksums",
            LedgerValueKind::Checksum,
        ),
        (
            "publication-ledger-signatures",
            "artifact signatures",
            "signatures",
            LedgerValueKind::Signature,
        ),
        (
            "publication-ledger-promotion",
            "promotion decision",
            "promotion_decision",
            LedgerValueKind::Promotion,
        ),
    ] {
        if !table.get(key).is_some_and(|value| toml_value_has_ledger_evidence(value, kind)) {
            findings.push(GateFinding::error(
                code,
                format!(
                    "publication ledger field `{key}` is missing or contains invalid {description} evidence"
                ),
            ));
        }
    }

    GateReport::new("publication-ledger", findings).with_evidence_refs([path.display().to_string()])
}

#[derive(Clone, Copy)]
enum LedgerValueKind {
    Tag,
    Checksum,
    Signature,
    Promotion,
}

fn toml_value_has_ledger_evidence(value: &toml::Value, kind: LedgerValueKind) -> bool {
    if matches!(kind, LedgerValueKind::Promotion) {
        return value.as_str().is_some_and(|value| ledger_string_has_evidence(value, kind));
    }
    let Some(values) = value.as_array() else {
        return false;
    };
    if values.is_empty() {
        return false;
    }
    let mut seen = std::collections::BTreeSet::new();
    values.iter().all(|value| {
        value.as_str().is_some_and(|value| {
            ledger_string_has_evidence(value, kind) && seen.insert(value.to_string())
        })
    })
}

fn ledger_string_has_evidence(value: &str, kind: LedgerValueKind) -> bool {
    let value = value.trim();
    if value.is_empty() || value.len() > 4096 || value.chars().any(char::is_control) {
        return false;
    }
    match kind {
        LedgerValueKind::Tag => value.strip_prefix("trust-v").is_some_and(|tag| {
            !tag.is_empty()
                && tag.as_bytes().first().is_some_and(u8::is_ascii_digit)
                && tag
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-'))
        }),
        LedgerValueKind::Checksum => {
            value.strip_prefix("sha256:").or(Some(value)).is_some_and(|sha| {
                sha.len() == 64
                    && sha
                        .bytes()
                        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            })
        }
        LedgerValueKind::Signature => {
            value
                .strip_prefix("sig:")
                .or_else(|| value.strip_prefix("minisig:"))
                .is_some_and(|payload| !payload.is_empty())
                || value
                    .strip_suffix(".sig")
                    .or_else(|| value.strip_suffix(".asc"))
                    .is_some_and(|stem| !stem.is_empty())
        }
        LedgerValueKind::Promotion => value == "promote",
    }
}

pub(super) fn channel_manifest_binds_artifact(
    value: &toml::Value,
    file_name: &str,
    sha256: &str,
) -> bool {
    match value {
        toml::Value::Table(table) => {
            let url_matches = ["xz_url", "url"].iter().any(|key| {
                table
                    .get(*key)
                    .and_then(toml::Value::as_str)
                    .is_some_and(|url| url.rsplit('/').next() == Some(file_name))
            });
            let hash_matches = ["xz_hash", "hash", "sha256"]
                .iter()
                .any(|key| table.get(*key).and_then(toml::Value::as_str) == Some(sha256));
            (url_matches && hash_matches)
                || table
                    .values()
                    .any(|value| channel_manifest_binds_artifact(value, file_name, sha256))
        }
        toml::Value::Array(values) => {
            values.iter().any(|value| channel_manifest_binds_artifact(value, file_name, sha256))
        }
        _ => false,
    }
}

pub(super) fn find_dist_artifact(
    root: &Path,
    prefix: &str,
    excludes: &[&str],
    channel_manifest: Option<&toml::Value>,
) -> Option<PathBuf> {
    const MAX_DIST_ENTRIES: usize = 100_000;
    const MAX_DIST_DEPTH: usize = 8;
    const MAX_DIST_ARTIFACT_BYTES: u64 = 32 * 1024 * 1024 * 1024;

    let root_metadata = fs::symlink_metadata(root).ok()?;
    if root_metadata.file_type().is_symlink() || !root_metadata.file_type().is_dir() {
        return None;
    }

    let mut pending = vec![(root.to_path_buf(), 0_usize)];
    let mut inspected = 0_usize;
    while let Some((directory, depth)) = pending.pop() {
        let mut entries = Vec::new();
        for entry in fs::read_dir(&directory).ok()? {
            inspected = inspected.checked_add(1)?;
            if inspected > MAX_DIST_ENTRIES {
                return None;
            }
            entries.push(entry.ok()?);
        }
        entries.sort_by_key(fs::DirEntry::file_name);
        // Stack traversal visits the lexically first entry first.
        entries.reverse();
        for entry in entries {
            let path = entry.path();
            let Some(metadata) = fs::symlink_metadata(&path).ok() else {
                continue;
            };
            if metadata.file_type().is_symlink() {
                continue;
            }
            if metadata.file_type().is_dir() {
                if depth >= MAX_DIST_DEPTH {
                    continue;
                }
                pending.push((path, depth + 1));
                continue;
            }
            if !metadata.file_type().is_file() {
                continue;
            }
            let Some(file_name) = path.file_name().and_then(|name| name.to_str()) else {
                continue;
            };
            if !(file_name.starts_with(prefix)
                && file_name
                    .strip_prefix(prefix)
                    .and_then(|suffix| suffix.as_bytes().first())
                    .is_some_and(u8::is_ascii_digit)
                && file_name.contains("-trust")
                && !excludes.iter().any(|exclude| file_name.starts_with(exclude))
                && is_release_artifact_name(file_name))
            {
                continue;
            }
            let Some((sha256, prefix_bytes)) =
                exact_file_sha256_with_prefix(&path, 8, Some(MAX_DIST_ARTIFACT_BYTES))
            else {
                continue;
            };
            if !artifact_has_expected_magic(file_name, &prefix_bytes) {
                continue;
            }
            if channel_manifest.is_some_and(|manifest| {
                channel_manifest_binds_artifact(manifest, file_name, &sha256)
            }) {
                return Some(path);
            }
        }
    }
    None
}

fn is_release_artifact_name(name: &str) -> bool {
    [".tar.xz", ".tar.gz", ".tgz", ".zip", ".pkg", ".msi"]
        .iter()
        .any(|suffix| name.ends_with(suffix))
}

fn artifact_has_expected_magic(name: &str, bytes: &[u8]) -> bool {
    if bytes.is_empty() {
        return false;
    }
    if name.ends_with(".tar.xz") {
        return bytes.starts_with(&[0xfd, b'7', b'z', b'X', b'Z', 0x00]);
    }
    if name.ends_with(".tar.gz") || name.ends_with(".tgz") {
        return bytes.starts_with(&[0x1f, 0x8b]);
    }
    if name.ends_with(".zip") {
        return bytes.starts_with(b"PK\x03\x04")
            || bytes.starts_with(b"PK\x05\x06")
            || bytes.starts_with(b"PK\x07\x08");
    }
    if name.ends_with(".pkg") {
        return bytes.starts_with(b"xar!");
    }
    if name.ends_with(".msi") {
        return bytes.starts_with(&[0xd0, 0xcf, 0x11, 0xe0, 0xa1, 0xb1, 0x1a, 0xe1]);
    }
    false
}
