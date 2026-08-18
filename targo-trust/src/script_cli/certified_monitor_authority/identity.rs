//! Canonical parsing of the shell payload manifest and identity v4.

use std::collections::{BTreeMap, BTreeSet};

use super::super::{CERTIFIED_MONITOR_PAYLOAD_FILES, CERTIFIED_MONITOR_PAYLOAD_IDENTITY_SCHEMA};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CertifiedMonitorPayloadIdentity {
    pub(super) stage2_sysroot: String,
    pub(super) trustc_sha256: String,
    pub(super) targo_sha256: String,
    pub(super) targo_trust_sha256: String,
    pub(super) trustd_sha256: String,
    pub(super) stage2_tree_sha256: String,
    pub(super) manifest_sha256: String,
    pub(super) lock_sha256: String,
    pub(super) trustc_commit: String,
    pub(super) targo_commit: String,
    pub(super) targo_trust_commit: String,
    pub(super) trustd_commit: String,
}

pub(super) fn parse_certified_monitor_evidence_manifest(
    bytes: &[u8],
) -> Result<Vec<(String, String)>, String> {
    if !bytes.ends_with(b"\n") {
        return Err("payload evidence manifest lacks its canonical final newline".to_string());
    }
    let text = std::str::from_utf8(bytes)
        .map_err(|_| "payload evidence manifest is not valid UTF-8".to_string())?;
    if text.contains('\r') {
        return Err("payload evidence manifest contains non-canonical CR bytes".to_string());
    }
    let lines = text.lines().collect::<Vec<_>>();
    if lines.len() != CERTIFIED_MONITOR_PAYLOAD_FILES.len() {
        return Err(format!(
            "payload evidence manifest must contain exactly {} entries, observed {}",
            CERTIFIED_MONITOR_PAYLOAD_FILES.len(),
            lines.len()
        ));
    }
    let mut names = BTreeSet::new();
    let mut rows = Vec::with_capacity(lines.len());
    for line in lines {
        if line.len() < 67 || line.get(64..66) != Some("  ") {
            return Err(format!("malformed payload evidence manifest row `{line}`"));
        }
        let digest = &line[..64];
        let name = &line[66..];
        if !is_canonical_sha256(digest) {
            return Err(format!("payload evidence manifest has malformed digest `{digest}`"));
        }
        if name.is_empty()
            || name.contains('/')
            || name.contains('\\')
            || name == "."
            || name == ".."
        {
            return Err(format!("payload evidence manifest has unsafe leaf `{name}`"));
        }
        if !names.insert(name.to_string()) {
            return Err(format!("payload evidence manifest repeats leaf `{name}`"));
        }
        rows.push((name.to_string(), digest.to_string()));
    }
    Ok(rows)
}

pub(super) fn parse_certified_monitor_payload_identity(
    bytes: &[u8],
    expected_head: &str,
) -> Result<CertifiedMonitorPayloadIdentity, String> {
    if !bytes.ends_with(b"\n") {
        return Err("payload gate identity lacks its canonical final newline".to_string());
    }
    let text = std::str::from_utf8(bytes)
        .map_err(|_| "payload gate identity is not valid UTF-8".to_string())?;
    if text.contains('\r') {
        return Err("payload gate identity contains non-canonical CR bytes".to_string());
    }
    let lines = text.lines().collect::<Vec<_>>();
    const SCALAR_KEYS: &[&str] = &[
        "schema",
        "result_scope",
        "source_authority",
        "head",
        "host_os",
        "host_arch",
        "stage2_sysroot",
        "trustc_sha256",
        "targo_sha256",
        "targo_trust_sha256",
        "trustd_sha256",
        "stage2_tree_sha256",
        "manifest_sha256",
        "lock_sha256",
        "targo_commit",
        "targo_trust_commit",
        "trustd_commit",
    ];
    let mut cursor = 0;
    let mut scalars = BTreeMap::new();
    for key in SCALAR_KEYS {
        let line = lines
            .get(cursor)
            .ok_or_else(|| format!("payload gate identity omits ordered scalar `{key}`"))?;
        let prefix = format!("{key}=");
        let value = line.strip_prefix(&prefix).ok_or_else(|| {
            format!(
                "payload gate identity expected ordered scalar `{key}` at row {}, observed `{line}`",
                cursor + 1
            )
        })?;
        if value.is_empty() {
            return Err(format!("payload gate identity scalar `{key}` is empty"));
        }
        scalars.insert(*key, value);
        cursor += 1;
    }
    let scalar = |key: &str| -> Result<&str, String> {
        scalars.get(key).copied().ok_or_else(|| format!("payload gate identity omits `{key}`"))
    };
    if scalar("schema")? != CERTIFIED_MONITOR_PAYLOAD_IDENTITY_SCHEMA
        || scalar("result_scope")? != "payload-only"
        || scalar("source_authority")? != "unverified"
    {
        return Err("payload gate identity has an unrecognized schema or authority scope".into());
    }
    if scalar("head")? != expected_head {
        return Err(format!(
            "payload gate identity HEAD {} differs from controlled-Git HEAD {expected_head}",
            scalar("head")?
        ));
    }
    if !matches!(
        (scalar("host_os")?, scalar("host_arch")?),
        ("Linux", "x86_64" | "aarch64") | ("Darwin", "x86_64" | "arm64")
    ) {
        return Err("payload gate identity records an unsupported host".to_string());
    }
    for key in [
        "trustc_sha256",
        "targo_sha256",
        "targo_trust_sha256",
        "trustd_sha256",
        "stage2_tree_sha256",
        "manifest_sha256",
        "lock_sha256",
    ] {
        if !is_canonical_sha256(scalar(key)?) {
            return Err(format!("payload gate identity has malformed `{key}`"));
        }
    }
    for key in ["targo_commit", "targo_trust_commit", "trustd_commit"] {
        if scalar(key)? != expected_head {
            return Err(format!(
                "payload gate identity `{key}` {} differs from controlled-Git HEAD {expected_head}",
                scalar(key)?
            ));
        }
    }

    let trustc_version = certified_monitor_identity_section(
        &lines,
        &mut cursor,
        "trustc_version_begin",
        "trustc_version_end",
    )?;
    let targo_version = certified_monitor_identity_section(
        &lines,
        &mut cursor,
        "targo_version_begin",
        "targo_version_end",
    )?;
    let targo_trust_version = certified_monitor_identity_section(
        &lines,
        &mut cursor,
        "targo_trust_version_begin",
        "targo_trust_version_end",
    )?;
    let trustd_version = certified_monitor_identity_section(
        &lines,
        &mut cursor,
        "trustd_version_begin",
        "trustd_version_end",
    )?;
    if cursor != lines.len() {
        return Err(format!(
            "payload gate identity has trailing rows after the final version block at row {}",
            cursor + 1
        ));
    }
    let trustc_commit = certified_monitor_unique_version_field(&trustc_version, "commit-hash")?;
    let targo_version_commit =
        certified_monitor_unique_version_field(&targo_version, "trust-repo-commit-hash")?;
    let targo_trust_version_commit =
        certified_monitor_unique_version_field(&targo_trust_version, "trust-repo-commit-hash")?;
    let trustd_version_commit =
        certified_monitor_unique_version_field(&trustd_version, "trust-repo-commit-hash")?;
    if trustc_commit != expected_head
        || targo_version_commit != expected_head
        || targo_trust_version_commit != expected_head
        || trustd_version_commit != expected_head
    {
        return Err(
            "payload gate identity version blocks are not all bound to controlled-Git HEAD"
                .to_string(),
        );
    }

    Ok(CertifiedMonitorPayloadIdentity {
        stage2_sysroot: scalar("stage2_sysroot")?.to_string(),
        trustc_sha256: scalar("trustc_sha256")?.to_string(),
        targo_sha256: scalar("targo_sha256")?.to_string(),
        targo_trust_sha256: scalar("targo_trust_sha256")?.to_string(),
        trustd_sha256: scalar("trustd_sha256")?.to_string(),
        stage2_tree_sha256: scalar("stage2_tree_sha256")?.to_string(),
        manifest_sha256: scalar("manifest_sha256")?.to_string(),
        lock_sha256: scalar("lock_sha256")?.to_string(),
        trustc_commit,
        targo_commit: scalar("targo_commit")?.to_string(),
        targo_trust_commit: scalar("targo_trust_commit")?.to_string(),
        trustd_commit: scalar("trustd_commit")?.to_string(),
    })
}

fn certified_monitor_identity_section(
    lines: &[&str],
    cursor: &mut usize,
    begin: &str,
    end: &str,
) -> Result<String, String> {
    let observed = lines.get(*cursor).copied().unwrap_or("<end-of-file>");
    if observed != begin {
        return Err(format!(
            "payload gate identity expected `{begin}` at row {}, observed `{observed}`",
            *cursor + 1
        ));
    }
    *cursor += 1;
    let body_start = *cursor;
    while let Some(line) = lines.get(*cursor) {
        if *line == end {
            break;
        }
        if is_certified_monitor_version_delimiter(line) {
            return Err(format!(
                "payload gate identity encountered version delimiter `{line}` before `{end}`"
            ));
        }
        *cursor += 1;
    }
    if *cursor == body_start || !lines[body_start..*cursor].iter().any(|line| !line.is_empty()) {
        return Err(format!("payload gate identity `{begin}` block has an empty body"));
    }
    if lines.get(*cursor).copied() != Some(end) {
        return Err(format!("payload gate identity omits `{end}`"));
    }
    let section = lines[body_start..*cursor].join("\n");
    *cursor += 1;
    Ok(section)
}

fn is_certified_monitor_version_delimiter(line: &str) -> bool {
    matches!(
        line,
        "trustc_version_begin"
            | "trustc_version_end"
            | "targo_version_begin"
            | "targo_version_end"
            | "targo_trust_version_begin"
            | "targo_trust_version_end"
            | "trustd_version_begin"
            | "trustd_version_end"
    )
}

fn certified_monitor_unique_version_field(section: &str, field: &str) -> Result<String, String> {
    let prefix = format!("{field}: ");
    let values = section.lines().filter_map(|line| line.strip_prefix(&prefix)).collect::<Vec<_>>();
    if values.len() != 1 || values[0].is_empty() {
        return Err(format!(
            "payload gate identity version block does not contain exactly one `{field}`"
        ));
    }
    Ok(values[0].to_string())
}

fn is_canonical_sha256(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
