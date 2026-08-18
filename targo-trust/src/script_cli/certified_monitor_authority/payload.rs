//! Stable, sealed-file validation for one certified-monitor payload directory.

use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::{fs, io};

use super::super::{
    CERTIFIED_MONITOR_EVIDENCE_MANIFEST, CERTIFIED_MONITOR_MAX_IDENTITY_BYTES,
    CERTIFIED_MONITOR_MAX_MANIFEST_BYTES, CERTIFIED_MONITOR_MAX_RETAINED_FILE_BYTES,
    CERTIFIED_MONITOR_PAYLOAD_FILES, same_stage2_file_identity,
};
use super::identity::{
    CertifiedMonitorPayloadIdentity, parse_certified_monitor_evidence_manifest,
    parse_certified_monitor_payload_identity,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::script_cli) struct ValidatedCertifiedMonitorPayload {
    pub(in crate::script_cli) evidence_directory: PathBuf,
    pub(super) evidence_manifest: PathBuf,
    pub(super) evidence_manifest_sha256: String,
    pub(super) identity_path: PathBuf,
    pub(super) identity_sha256: String,
    pub(super) identity: CertifiedMonitorPayloadIdentity,
}

pub(super) fn validate_certified_monitor_payload(
    requested_directory: &Path,
    expected_head: &str,
) -> Result<ValidatedCertifiedMonitorPayload, String> {
    let before = fs::symlink_metadata(requested_directory).map_err(|error| {
        format!(
            "cannot inspect payload evidence directory {}: {error}",
            requested_directory.display()
        )
    })?;
    if before.file_type().is_symlink() || !before.file_type().is_dir() {
        return Err(format!(
            "payload evidence directory is not an exact directory: {}",
            requested_directory.display()
        ));
    }
    require_certified_monitor_sealed_metadata(
        &before,
        0o500,
        "payload evidence directory",
        requested_directory,
    )?;
    let evidence_directory = fs::canonicalize(requested_directory).map_err(|error| {
        format!(
            "cannot canonicalize payload evidence directory {}: {error}",
            requested_directory.display()
        )
    })?;
    if evidence_directory != requested_directory {
        return Err(format!(
            "payload evidence directory contains a non-canonical or symlinked path component: requested {}, canonical {}",
            requested_directory.display(),
            evidence_directory.display()
        ));
    }

    let expected_entries = CERTIFIED_MONITOR_PAYLOAD_FILES
        .iter()
        .copied()
        .chain(std::iter::once(CERTIFIED_MONITOR_EVIDENCE_MANIFEST))
        .map(str::to_string)
        .collect::<BTreeSet<_>>();
    let observed_entries = certified_monitor_directory_entries(&evidence_directory)?;
    if observed_entries != expected_entries {
        return Err(format!(
            "payload evidence directory does not contain the exact reviewed file set (expected {expected_entries:?}, observed {observed_entries:?})"
        ));
    }

    let evidence_manifest = evidence_directory.join(CERTIFIED_MONITOR_EVIDENCE_MANIFEST);
    let (manifest_bytes, evidence_manifest_sha256) = read_stable_certified_monitor_file(
        &evidence_manifest,
        "payload evidence manifest",
        CERTIFIED_MONITOR_MAX_MANIFEST_BYTES,
    )?;
    let manifest_rows = parse_certified_monitor_evidence_manifest(&manifest_bytes)?;

    for ((expected_name, expected_digest), reviewed_name) in
        manifest_rows.iter().zip(CERTIFIED_MONITOR_PAYLOAD_FILES)
    {
        if expected_name != reviewed_name {
            return Err(format!(
                "payload evidence manifest entry is out of canonical order: expected `{reviewed_name}`, observed `{expected_name}`"
            ));
        }
        let path = evidence_directory.join(reviewed_name);
        let observed_digest = hash_stable_certified_monitor_file(
            &path,
            &format!("payload evidence `{reviewed_name}`"),
            CERTIFIED_MONITOR_MAX_RETAINED_FILE_BYTES,
        )?;
        if &observed_digest != expected_digest {
            return Err(format!(
                "payload evidence digest mismatch for `{reviewed_name}`: manifest {expected_digest}, observed {observed_digest}"
            ));
        }
    }

    let identity_path = evidence_directory.join(CERTIFIED_MONITOR_PAYLOAD_FILES[0]);
    let (identity_bytes, identity_sha256) = read_stable_certified_monitor_file(
        &identity_path,
        "payload gate identity",
        CERTIFIED_MONITOR_MAX_IDENTITY_BYTES,
    )?;
    let identity = parse_certified_monitor_payload_identity(&identity_bytes, expected_head)?;

    // Reopen the two authority-bearing indexes after all retained logs have
    // been hashed so a concurrent replacement cannot win by changing either
    // the manifest or identity during the validation walk.
    let terminal_manifest_sha256 = hash_stable_certified_monitor_file(
        &evidence_manifest,
        "terminal payload evidence manifest",
        CERTIFIED_MONITOR_MAX_MANIFEST_BYTES,
    )?;
    let terminal_identity_sha256 = hash_stable_certified_monitor_file(
        &identity_path,
        "terminal payload gate identity",
        CERTIFIED_MONITOR_MAX_IDENTITY_BYTES,
    )?;
    if terminal_manifest_sha256 != evidence_manifest_sha256
        || terminal_identity_sha256 != identity_sha256
    {
        return Err("payload evidence manifest or identity changed during native validation".into());
    }
    let terminal_entries = certified_monitor_directory_entries(&evidence_directory)?;
    let after = fs::symlink_metadata(&evidence_directory)
        .map_err(|error| format!("cannot re-inspect payload evidence directory: {error}"))?;
    require_certified_monitor_sealed_metadata(
        &after,
        0o500,
        "terminal payload evidence directory",
        &evidence_directory,
    )?;
    if !same_stage2_file_identity(&before, &after) || terminal_entries != expected_entries {
        return Err("payload evidence directory changed during native validation".to_string());
    }

    Ok(ValidatedCertifiedMonitorPayload {
        evidence_directory,
        evidence_manifest,
        evidence_manifest_sha256,
        identity_path,
        identity_sha256,
        identity,
    })
}

fn certified_monitor_directory_entries(directory: &Path) -> Result<BTreeSet<String>, String> {
    let mut entries = BTreeSet::new();
    let reader = fs::read_dir(directory).map_err(|error| {
        format!("cannot enumerate payload evidence directory {}: {error}", directory.display())
    })?;
    for entry in reader {
        let entry = entry.map_err(|error| {
            format!("cannot enumerate payload evidence directory {}: {error}", directory.display())
        })?;
        let name = entry
            .file_name()
            .into_string()
            .map_err(|_| "payload evidence contains a non-UTF-8 file name".to_string())?;
        if !entries.insert(name.clone()) {
            return Err(format!("payload evidence repeats directory entry `{name}`"));
        }
    }
    Ok(entries)
}

pub(super) fn read_stable_certified_monitor_file(
    path: &Path,
    label: &str,
    max_bytes: u64,
) -> Result<(Vec<u8>, String), String> {
    let (mut file, before) = open_stable_certified_monitor_file(path, label, max_bytes)?;
    let mut bytes = Vec::with_capacity(usize::try_from(before.len()).unwrap_or(0));
    (&mut file)
        .take(max_bytes.saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read {label} {}: {error}", path.display()))?;
    if bytes.len() as u64 != before.len() {
        return Err(format!("{label} changed length while being read: {}", path.display()));
    }
    finish_stable_certified_monitor_file(path, label, &before)?;
    let digest = format!("{:x}", Sha256::digest(&bytes));
    Ok((bytes, digest))
}

fn hash_stable_certified_monitor_file(
    path: &Path,
    label: &str,
    max_bytes: u64,
) -> Result<String, String> {
    let (mut file, before) = open_stable_certified_monitor_file(path, label, max_bytes)?;
    let mut hasher = Sha256::new();
    let copied = io::copy(&mut (&mut file).take(max_bytes.saturating_add(1)), &mut hasher)
        .map_err(|error| format!("cannot hash {label} {}: {error}", path.display()))?;
    if copied != before.len() {
        return Err(format!("{label} changed length while being hashed: {}", path.display()));
    }
    finish_stable_certified_monitor_file(path, label, &before)?;
    Ok(format!("{:x}", hasher.finalize()))
}

fn open_stable_certified_monitor_file(
    path: &Path,
    label: &str,
    max_bytes: u64,
) -> Result<(fs::File, fs::Metadata), String> {
    let before = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {label} {}: {error}", path.display()))?;
    if before.file_type().is_symlink() || !before.file_type().is_file() {
        return Err(format!("{label} is not an exact regular file: {}", path.display()));
    }
    require_certified_monitor_sealed_metadata(&before, 0o400, label, path)?;
    if before.len() > max_bytes {
        return Err(format!("{label} exceeds the {max_bytes}-byte limit: {}", path.display()));
    }
    let file = fs::File::open(path)
        .map_err(|error| format!("cannot open {label} {}: {error}", path.display()))?;
    let opened = file
        .metadata()
        .map_err(|error| format!("cannot inspect open {label} {}: {error}", path.display()))?;
    if !opened.file_type().is_file()
        || !same_stage2_file_identity(&before, &opened)
        || opened.len() != before.len()
    {
        return Err(format!("{label} changed while being opened: {}", path.display()));
    }
    require_certified_monitor_sealed_metadata(&opened, 0o400, label, path)?;
    Ok((file, before))
}

fn finish_stable_certified_monitor_file(
    path: &Path,
    label: &str,
    before: &fs::Metadata,
) -> Result<(), String> {
    let after = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot re-inspect {label} {}: {error}", path.display()))?;
    if after.file_type().is_symlink()
        || !after.file_type().is_file()
        || !same_stage2_file_identity(before, &after)
        || after.len() != before.len()
    {
        return Err(format!("{label} changed during validation: {}", path.display()));
    }
    require_certified_monitor_sealed_metadata(&after, 0o400, label, path)
}

#[cfg(unix)]
fn require_certified_monitor_sealed_metadata(
    metadata: &fs::Metadata,
    expected_mode: u32,
    label: &str,
    path: &Path,
) -> Result<(), String> {
    use std::os::unix::fs::MetadataExt as _;

    let mode = metadata.mode() & 0o777;
    let owner = metadata.uid();
    let links = metadata.nlink();
    let expected_owner = unsafe { libc::geteuid() };
    if mode != expected_mode || owner != expected_owner {
        return Err(format!(
            "{label} is not sealed to owner {expected_owner} mode {expected_mode:04o}: {} has owner {owner} mode {mode:04o}",
            path.display()
        ));
    }
    if expected_mode == 0o400 && links != 1 {
        return Err(format!(
            "{label} is not an unaliased sealed regular file: {} has link count {links}, expected 1",
            path.display()
        ));
    }
    Ok(())
}

#[cfg(not(unix))]
fn require_certified_monitor_sealed_metadata(
    _metadata: &fs::Metadata,
    _expected_mode: u32,
    label: &str,
    path: &Path,
) -> Result<(), String> {
    Err(format!(
        "{label} cannot be authenticated on this host: Unix owner and mode semantics are required: {}",
        path.display()
    ))
}
