use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, OpenOptions};
use std::io::{self, Read as _};
use std::path::{Component, Path};

#[cfg(unix)]
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};

use sha2::{Digest as _, Sha256};
use trust_release::{GateFinding, GateReport};

use crate::input_limits::{MAX_RELEASE_METADATA_BYTES, read_bounded_utf8_file};

use super::types::ReleaseProfile;

const REQUIRED_PAYLOAD_FAMILIES: &[(&str, &str)] = &[
    ("targo-", "compiler_version"),
    ("targo-trust-", "compiler_version"),
    ("tippy-", "compiler_version"),
    ("trust-analyzer-", "compiler_version"),
    ("trust-src-", "compiler_version"),
    ("trust-std-", "compiler_version"),
    ("trustc-", "compiler_version"),
    ("trustc-dev-", "compiler_version"),
    ("trustfmt-", "rustfmt_version"),
];

pub(super) fn check_seed_freshness(root: &Path, profile: ReleaseProfile) -> GateReport {
    let release = profile.requires_bound_tools();
    let mut findings = Vec::new();
    let source_text =
        match read_bounded_utf8_file(&root.join("src/version"), MAX_RELEASE_METADATA_BYTES) {
            Ok(text) => text,
            Err(error) => {
                findings.push(finding(
                    release,
                    "seed-source-version-unreadable",
                    format!("could not read src/version: {error}"),
                ));
                return report(findings);
            }
        };
    let source_version = match parse_version(source_text.trim()) {
        Some(version) => version,
        None => {
            findings.push(finding(
                release,
                "seed-source-version-invalid",
                format!("src/version is not a complete semantic version: {:?}", source_text.trim()),
            ));
            return report(findings);
        }
    };

    let stage0_text =
        match read_bounded_utf8_file(&root.join("src/stage0"), MAX_RELEASE_METADATA_BYTES) {
            Ok(text) => text,
            Err(error) => {
                findings.push(finding(
                    release,
                    "seed-metadata-unreadable",
                    format!("could not read src/stage0: {error}"),
                ));
                return report(findings);
            }
        };
    let stage0 = match parse_stage0(&stage0_text) {
        Ok(fields) => fields,
        Err(error) => {
            findings.push(finding(release, "seed-metadata-invalid", error));
            return report(findings);
        }
    };

    validate_metadata(&stage0, release, &mut findings);
    match stage0.get("compiler_version").and_then(|value| parse_version(value)) {
        Some((seed_major, seed_minor))
            if seed_major == source_version.0
                && (seed_minor == source_version.1
                    || seed_minor.checked_add(1) == Some(source_version.1)) => {}
        Some((seed_major, seed_minor)) => findings.push(finding(
            release,
            "seed-cadence-stale",
            format!(
                "seed {seed_major}.{seed_minor} is not source {}.{} or its immediate predecessor",
                source_version.0, source_version.1
            ),
        )),
        None => findings.push(finding(
            release,
            "seed-version-invalid",
            "compiler_version in src/stage0 is not a complete semantic version".to_string(),
        )),
    }

    if release {
        validate_payloads(root, &stage0, &mut findings);
    }
    report(findings)
}

fn report(findings: Vec<GateFinding>) -> GateReport {
    GateReport::new("seed-freshness", findings).with_evidence_refs([
        "src/version",
        "src/stage0",
        "bootstrap/trust-stage0/dist",
    ])
}

fn finding(release: bool, code: &str, message: String) -> GateFinding {
    if release { GateFinding::error(code, message) } else { GateFinding::warning(code, message) }
}

fn parse_version(value: &str) -> Option<(u64, u64)> {
    let (without_build, build) =
        value.split_once('+').map_or((value, None), |(core, build)| (core, Some(build)));
    if build.is_some_and(|build| build.contains('+') || !valid_semver_identifiers(build, false)) {
        return None;
    }
    let (core, prerelease) = without_build
        .split_once('-')
        .map_or((without_build, None), |(core, prerelease)| (core, Some(prerelease)));
    if prerelease.is_some_and(|prerelease| !valid_semver_identifiers(prerelease, true)) {
        return None;
    }
    let mut parts = core.split('.');
    let major = parse_semver_number(parts.next()?)?;
    let minor = parse_semver_number(parts.next()?)?;
    parse_semver_number(parts.next()?)?;
    if parts.next().is_some() {
        return None;
    }
    Some((major, minor))
}

fn valid_semver_identifiers(value: &str, reject_numeric_leading_zero: bool) -> bool {
    !value.is_empty()
        && value.split('.').all(|identifier| {
            !identifier.is_empty()
                && identifier.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
                && !(reject_numeric_leading_zero
                    && identifier.len() > 1
                    && identifier.bytes().all(|byte| byte.is_ascii_digit())
                    && identifier.starts_with('0'))
        })
}

fn parse_semver_number(value: &str) -> Option<u64> {
    if value.is_empty() || (value.len() > 1 && value.starts_with('0')) {
        return None;
    }
    value.parse().ok()
}

fn parse_stage0(input: &str) -> Result<BTreeMap<String, String>, String> {
    let mut fields = BTreeMap::new();
    for (index, raw) in input.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            return Err(format!("src/stage0:{} is not a key=value record", index + 1));
        };
        let (key, value) = (key.trim(), value.trim());
        if key.is_empty() || value.is_empty() {
            return Err(format!("src/stage0:{} has an empty key or value", index + 1));
        }
        if fields.insert(key.to_string(), value.to_string()).is_some() {
            return Err(format!("src/stage0:{} repeats key {key:?}", index + 1));
        }
    }
    Ok(fields)
}

fn validate_metadata(
    stage0: &BTreeMap<String, String>,
    release: bool,
    findings: &mut Vec<GateFinding>,
) {
    for component in ["compiler", "rustfmt"] {
        let version = stage0.get(&format!("{component}_version")).map(String::as_str).unwrap_or("");
        if parse_version(version).is_none() {
            findings.push(finding(
                release,
                "seed-metadata-version-invalid",
                format!("{component}_version is not a complete semantic version"),
            ));
        }
        let commit =
            stage0.get(&format!("{component}_git_commit_hash")).map(String::as_str).unwrap_or("");
        if !is_lower_hex(commit, 40) {
            findings.push(finding(
                release,
                "seed-metadata-commit-invalid",
                format!("{component}_git_commit_hash is not canonical lowercase SHA-1"),
            ));
        }
        let date = stage0.get(&format!("{component}_date")).map(String::as_str).unwrap_or("");
        if !valid_date(date) {
            findings.push(finding(
                release,
                "seed-metadata-date-invalid",
                format!("{component}_date is not a valid canonical YYYY-MM-DD date"),
            ));
        }
        let manifest_hash = stage0
            .get(&format!("{component}_channel_manifest_hash"))
            .map(String::as_str)
            .unwrap_or("");
        if !is_lower_hex(manifest_hash, 64) {
            findings.push(finding(
                release,
                "seed-metadata-manifest-hash-invalid",
                format!("{component}_channel_manifest_hash is not canonical SHA-256"),
            ));
        }
    }
    if stage0.get("compiler_date") != stage0.get("rustfmt_date") {
        findings.push(finding(
            release,
            "seed-metadata-snapshot-mismatch",
            "compiler_date and rustfmt_date do not identify one seed snapshot".to_string(),
        ));
    }
}

fn validate_payloads(
    root: &Path,
    stage0: &BTreeMap<String, String>,
    findings: &mut Vec<GateFinding>,
) {
    let date = stage0.get("compiler_date").map(String::as_str).unwrap_or("");
    let prefix = format!("dist/{date}/");
    let declared = stage0
        .iter()
        .filter(|(key, _)| key.starts_with(&prefix) && key.ends_with(".tar.xz"))
        .collect::<Vec<_>>();
    if declared.is_empty() {
        findings.push(GateFinding::error(
            "seed-payload-inventory-empty",
            format!("src/stage0 declares no payloads under {prefix}"),
        ));
        return;
    }

    let filenames = declared
        .iter()
        .filter_map(|(key, _)| Path::new(key).file_name().and_then(|name| name.to_str()))
        .collect::<BTreeSet<_>>();
    for &(family, version_key) in REQUIRED_PAYLOAD_FAMILIES {
        let version = stage0.get(version_key).map(String::as_str).unwrap_or("");
        let present =
            filenames.iter().any(|name| payload_archive_name_matches(name, family, version));
        if !present {
            findings.push(GateFinding::error(
                "seed-payload-family-missing",
                format!(
                    "declared payload inventory has no {} archive bound to {version_key}={version}",
                    family.trim_end_matches('-'),
                ),
            ));
        }
    }

    let base = root.join("bootstrap/trust-stage0");
    for (relative, expected) in declared {
        if !safe_relative_path(relative) {
            findings.push(GateFinding::error(
                "seed-payload-path-invalid",
                format!("declared payload path is not canonical and relative: {relative}"),
            ));
            continue;
        }
        if !is_lower_hex(expected, 64) {
            findings.push(GateFinding::error(
                "seed-payload-hash-invalid",
                format!("declared payload digest is not canonical SHA-256: {relative}"),
            ));
            continue;
        }
        match regular_file_sha256_under(&base, Path::new(relative)) {
            Ok(observed) if observed == expected.as_str() => {}
            Ok(observed) => findings.push(GateFinding::error(
                "seed-payload-hash-mismatch",
                format!("{relative} digest mismatch: expected {expected}, observed {observed}"),
            )),
            Err(error) => findings.push(GateFinding::error(
                "seed-payload-missing",
                format!("could not authenticate {relative}: {error}"),
            )),
        }
    }

    let manifest_relative = format!("dist/{date}/channel-rust-trust.toml");
    match regular_file_sha256_under(&base, Path::new(&manifest_relative)) {
        Ok(observed) => {
            for component in ["compiler", "rustfmt"] {
                let expected = stage0
                    .get(&format!("{component}_channel_manifest_hash"))
                    .map(String::as_str)
                    .unwrap_or("");
                if is_lower_hex(expected, 64) && observed != expected {
                    findings.push(GateFinding::error(
                        "seed-manifest-hash-mismatch",
                        format!(
                            "{manifest_relative} does not match {component}_channel_manifest_hash"
                        ),
                    ));
                }
            }
        }
        Err(error) => findings.push(GateFinding::error(
            "seed-manifest-missing",
            format!("could not authenticate {manifest_relative}: {error}"),
        )),
    }
}

fn payload_archive_name_matches(name: &str, family: &str, version: &str) -> bool {
    if version.is_empty() {
        return false;
    }
    let expected_prefix = format!("{family}{version}");
    let Some(suffix) = name.strip_prefix(&expected_prefix) else {
        return false;
    };
    if suffix == ".tar.xz" {
        return true;
    }
    let Some(target) = suffix.strip_prefix('-').and_then(|value| value.strip_suffix(".tar.xz"))
    else {
        return false;
    };
    target.as_bytes().first().is_some_and(u8::is_ascii_alphanumeric)
        && target.as_bytes().last().is_some_and(u8::is_ascii_alphanumeric)
        && !target.contains("..")
        && target
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
}

fn is_lower_hex(value: &str, len: usize) -> bool {
    value.len() == len
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn valid_date(value: &str) -> bool {
    let bytes = value.as_bytes();
    if bytes.len() != 10 || bytes[4] != b'-' || bytes[7] != b'-' {
        return false;
    }
    let parse = |range: std::ops::Range<usize>| {
        std::str::from_utf8(&bytes[range]).ok()?.parse::<u32>().ok()
    };
    let (Some(year), Some(month), Some(day)) = (parse(0..4), parse(5..7), parse(8..10)) else {
        return false;
    };
    if year == 0 {
        return false;
    }
    let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    let max_day = match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if leap => 29,
        2 => 28,
        _ => return false,
    };
    (1..=max_day).contains(&day)
}

fn safe_relative_path(path: &str) -> bool {
    let path = Path::new(path);
    !path.is_absolute()
        && path.components().all(|component| matches!(component, Component::Normal(_)))
}

fn regular_file_sha256_under(base: &Path, relative: &Path) -> io::Result<String> {
    if relative.as_os_str().is_empty()
        || relative.is_absolute()
        || !relative.components().all(|component| matches!(component, Component::Normal(_)))
    {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, "not a safe relative path"));
    }
    let components = relative.components().collect::<Vec<_>>();
    let mut path = base.to_path_buf();
    for (index, component) in components.iter().enumerate() {
        path.push(component.as_os_str());
        let metadata = fs::symlink_metadata(&path)?;
        let is_last = index + 1 == components.len();
        if (is_last && !metadata.file_type().is_file())
            || (!is_last && !metadata.file_type().is_dir())
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "path contains a symlink or a component of the wrong type",
            ));
        }
    }
    let expected_metadata = fs::symlink_metadata(&path)?;
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    options.custom_flags(libc::O_CLOEXEC | libc::O_NOFOLLOW);
    let mut file = options.open(&path)?;
    let opened_metadata = file.metadata()?;
    if !opened_metadata.file_type().is_file()
        || !same_payload_snapshot(&expected_metadata, &opened_metadata)
    {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "opened payload is not a file"));
    }
    let mut digest = Sha256::new();
    let mut buffer = [0_u8; 64 * 1024];
    let mut total = 0_u64;
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        total = total
            .checked_add(read as u64)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "payload size overflow"))?;
        if total > expected_metadata.len() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "payload grew while it was being authenticated",
            ));
        }
        digest.update(&buffer[..read]);
    }
    if total != expected_metadata.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "payload size changed while it was being authenticated",
        ));
    }
    let opened_after = file.metadata()?;
    let path_after = fs::symlink_metadata(&path)?;
    if path_after.file_type().is_symlink()
        || !path_after.file_type().is_file()
        || !same_payload_snapshot(&expected_metadata, &opened_after)
        || !same_payload_snapshot(&expected_metadata, &path_after)
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "payload changed while it was being authenticated",
        ));
    }
    Ok(format!("{:x}", digest.finalize()))
}

#[cfg(unix)]
fn same_payload_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.len() == right.len()
        && left.mode() == right.mode()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

#[cfg(not(unix))]
fn same_payload_snapshot(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file()
        && right.is_file()
        && left.len() == right.len()
        && left.modified().ok() == right.modified().ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::release_cli::release_gate_filter_includes;
    use crate::release_cli::types::ReleaseVisibility;
    use trust_release::GateStatus;

    #[test]
    fn version_and_date_parsers_are_complete_and_canonical() {
        assert_eq!(parse_version("1.99.0-trust"), Some((1, 99)));
        assert_eq!(parse_version("1.99"), None);
        assert_eq!(parse_version("1.99.0-trust!"), None);
        assert_eq!(parse_version("01.99.0"), None);
        assert_eq!(parse_version("1.099.0"), None);
        assert_eq!(parse_version("1.99.00"), None);
        assert_eq!(parse_version("1.99.0-trust..seed"), None);
        assert_eq!(parse_version("1.99.0-trust.01"), None);
        assert_eq!(parse_version("1.99.0-trust.1+seed.01"), Some((1, 99)));
        assert_eq!(parse_version("1.99.0+seed.01"), Some((1, 99)));
        assert_eq!(parse_version("1.99.0+"), None);
        assert_eq!(parse_version("1.99.0+seed+again"), None);
        assert!(valid_date("2024-02-29"));
        assert!(!valid_date("2025-02-29"));
        assert!(!valid_date("2025-2-09"));
    }

    #[test]
    fn payload_inventory_names_are_bound_to_the_declared_version() {
        let version = "1.99.0-trust";
        assert!(payload_archive_name_matches(
            "trustc-1.99.0-trust-aarch64-apple-darwin.tar.xz",
            "trustc-",
            version,
        ));
        assert!(payload_archive_name_matches(
            "trust-src-1.99.0-trust.tar.xz",
            "trust-src-",
            version,
        ));
        assert!(!payload_archive_name_matches("trustc-garbage.tar.xz", "trustc-", version,));
        assert!(!payload_archive_name_matches(
            "trustc-1.98.0-trust-aarch64-apple-darwin.tar.xz",
            "trustc-",
            version,
        ));
        assert!(!payload_archive_name_matches(
            "trustc-dev-1.99.0-trust-aarch64-apple-darwin.tar.xz",
            "trustc-",
            version,
        ));
        assert!(!payload_archive_name_matches(
            "targo-trust-1.99.0-trust-aarch64-apple-darwin.tar.xz",
            "targo-",
            version,
        ));
        assert!(!payload_archive_name_matches(
            "trustc-1.99.0-trust-../../escape.tar.xz",
            "trustc-",
            version,
        ));
        for target in [
            ".x86_64-unknown-linux-gnu",
            "_x86_64-unknown-linux-gnu",
            "-x86_64-unknown-linux-gnu",
            "x86_64-unknown-linux-gnu.",
            "x86_64..unknown-linux-gnu",
        ] {
            assert!(!payload_archive_name_matches(
                &format!("trustc-{version}-{target}.tar.xz"),
                "trustc-",
                version,
            ));
        }
    }

    #[test]
    fn stage0_parser_rejects_duplicates_and_non_records() {
        assert!(parse_stage0("a=1\na=2\n").is_err());
        assert!(parse_stage0("not-a-record\n").is_err());
        assert_eq!(parse_stage0("# comment\na=1\n").unwrap()["a"], "1");
    }

    #[test]
    fn publication_gate_filters_cannot_bypass_seed_authentication() {
        assert!(release_gate_filter_includes(
            ReleaseProfile::Publication,
            ReleaseVisibility::Private,
            "owned-deps",
            "seed-freshness"
        ));
        assert!(!release_gate_filter_includes(
            ReleaseProfile::Metadata,
            ReleaseVisibility::Private,
            "owned-deps",
            "seed-freshness"
        ));
    }

    #[test]
    fn metadata_profile_warns_but_publication_requires_payloads() {
        let root = tempfile::tempdir().expect("seed fixture");
        fs::create_dir_all(root.path().join("src")).expect("src");
        fs::write(root.path().join("src/version"), "1.99.0\n").expect("version");
        let hash = "0".repeat(64);
        let commit = "1".repeat(40);
        fs::write(
            root.path().join("src/stage0"),
            format!(
                "compiler_version=1.96.0-trust\ncompiler_git_commit_hash={commit}\ncompiler_date=2026-07-06\ncompiler_channel_manifest_hash={hash}\nrustfmt_version=1.96.0-trust\nrustfmt_git_commit_hash={commit}\nrustfmt_date=2026-07-06\nrustfmt_channel_manifest_hash={hash}\n"
            ),
        )
        .expect("stage0");

        assert_eq!(
            check_seed_freshness(root.path(), ReleaseProfile::Metadata).status,
            GateStatus::Warn
        );
        let publication = check_seed_freshness(root.path(), ReleaseProfile::Publication);
        assert_eq!(publication.status, GateStatus::Fail);
        assert!(publication.findings.iter().any(|finding| {
            finding.code == "seed-cadence-stale" || finding.code == "seed-payload-inventory-empty"
        }));
    }

    #[cfg(unix)]
    #[test]
    fn payload_authentication_rejects_symlink_files_and_directories() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().expect("seed authentication fixture");
        fs::create_dir_all(root.path().join("real/dist")).expect("real directory");
        fs::write(root.path().join("real/dist/payload"), b"payload").expect("payload");
        symlink(root.path().join("real/dist/payload"), root.path().join("payload"))
            .expect("file symlink");
        assert!(regular_file_sha256_under(root.path(), Path::new("payload")).is_err());

        symlink(root.path().join("real"), root.path().join("linked")).expect("directory symlink");
        assert!(regular_file_sha256_under(root.path(), Path::new("linked/dist/payload")).is_err());
    }
}
