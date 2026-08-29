//! Native authority binding for the certified-monitor Layer-3b payload.

use std::path::{Path, PathBuf};
use std::{fs, io};

use serde::Serialize;

use super::{
    CERTIFIED_MONITOR_LOG_DIR_ENV, CERTIFIED_MONITOR_MAX_IDENTITY_BYTES,
    CERTIFIED_MONITOR_NATIVE_AUTHORITY_SCHEMA, CERTIFIED_MONITOR_PAYLOAD_FILES,
    CERTIFIED_MONITOR_PAYLOAD_IDENTITY_SCHEMA, CERTIFIED_MONITOR_RUN_ID_ENV,
};

mod identity;
mod payload;
mod publication;
#[cfg(test)]
mod tests;
use payload::{
    ValidatedCertifiedMonitorPayload, validate_certified_monitor_payload as validate_payload,
};
pub(super) use publication::publish_certified_monitor_native_authority_receipt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct CertifiedMonitorEvidenceLayout {
    pub(super) payload_directory: PathBuf,
    pub(super) authority_receipt: PathBuf,
}

pub(super) fn certified_monitor_evidence_layout(
    repo_root: &Path,
    args: &[String],
    head: &str,
    inherited_log_directory: Option<std::ffi::OsString>,
    inherited_run_id: Option<std::ffi::OsString>,
) -> Result<CertifiedMonitorEvidenceLayout, String> {
    let mut requested_log_directory = None;
    let mut index = 0;
    while index < args.len() {
        if args[index] == "--log-dir" {
            let value =
                args.get(index + 1).ok_or_else(|| "--log-dir requires one path".to_string())?;
            if requested_log_directory.replace(value.clone()).is_some() {
                return Err("--log-dir may be supplied at most once".to_string());
            }
            index += 2;
        } else {
            index += 1;
        }
    }

    let requested = if let Some(requested) = requested_log_directory {
        if requested.is_empty() {
            return Err("--log-dir must not be empty".to_string());
        }
        PathBuf::from(requested)
    } else if let Some(requested) = inherited_log_directory {
        if requested.is_empty() {
            return Err(format!("{CERTIFIED_MONITOR_LOG_DIR_ENV} must not be empty"));
        }
        PathBuf::from(requested)
    } else {
        let run_id = if let Some(run_id) = inherited_run_id {
            let run_id = run_id
                .into_string()
                .map_err(|_| format!("{CERTIFIED_MONITOR_RUN_ID_ENV} is not valid UTF-8"))?;
            validate_certified_monitor_run_id(&run_id)?;
            run_id
        } else {
            let elapsed = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_err(|_| "system clock precedes the Unix epoch".to_string())?;
            let short_head = head.get(..12).ok_or_else(|| {
                "controlled-Git HEAD is too short for an evidence identity".to_string()
            })?;
            format!(
                "stage2-certified-monitor-e2e-native-{short_head}-{}-{}",
                std::process::id(),
                elapsed.as_nanos()
            )
        };
        validate_certified_monitor_run_id(&run_id)?;
        repo_root.join("reports/build").join(run_id)
    };

    let payload_directory =
        if requested.is_absolute() { requested } else { repo_root.join(requested) };
    if payload_directory == repo_root || payload_directory.file_name().is_none() {
        return Err(format!(
            "payload evidence directory is not one safe leaf: {}",
            payload_directory.display()
        ));
    }
    if payload_directory.to_str().is_none() {
        return Err("payload evidence directory is not valid UTF-8".to_string());
    }
    let authority_receipt = certified_monitor_authority_receipt_path(&payload_directory);
    Ok(CertifiedMonitorEvidenceLayout { payload_directory, authority_receipt })
}

fn validate_certified_monitor_run_id(run_id: &str) -> Result<(), String> {
    let bytes = run_id.as_bytes();
    let valid = (1..=128).contains(&bytes.len())
        && bytes[0].is_ascii_alphanumeric()
        && bytes
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-'))
        && run_id != "."
        && run_id != "..";
    if valid {
        Ok(())
    } else {
        Err("certified-monitor run id must be one bounded filesystem-safe token".to_string())
    }
}

pub(super) fn certified_monitor_authority_receipt_path(payload_directory: &Path) -> PathBuf {
    let mut name = payload_directory.as_os_str().to_os_string();
    name.push(".native-authority.json");
    PathBuf::from(name)
}

pub(super) fn preflight_certified_monitor_evidence_layout(
    layout: &CertifiedMonitorEvidenceLayout,
) -> Result<(), String> {
    require_certified_monitor_native_authority_host()?;

    for (path, label) in [
        (&layout.payload_directory, "payload evidence directory"),
        (&layout.authority_receipt, "native authority receipt"),
    ] {
        match fs::symlink_metadata(path) {
            Ok(_) => {
                return Err(format!(
                    "{label} must not preexist or be reusable: {}",
                    path.display()
                ));
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!("cannot inspect {label} {}: {error}", path.display()));
            }
        }
    }
    Ok(())
}

#[cfg(unix)]
fn require_certified_monitor_native_authority_host() -> Result<(), String> {
    Ok(())
}

#[cfg(not(unix))]
fn require_certified_monitor_native_authority_host() -> Result<(), String> {
    Err(
        "certified-monitor native authority is unsupported on this host: Unix owner and mode semantics are required"
            .to_string(),
    )
}

pub(super) fn validate_certified_monitor_payload(
    requested_directory: &Path,
    expected_head: &str,
) -> Result<ValidatedCertifiedMonitorPayload, String> {
    validate_payload(requested_directory, expected_head)
}

#[derive(Serialize)]
struct CertifiedMonitorNativeAuthorityReceipt<'a> {
    schema: &'static str,
    status: &'static str,
    result_scope: &'static str,
    source_authority: &'static str,
    head: &'a str,
    repository_root: String,
    authority_receipt_path: String,
    authority: CertifiedMonitorNativeSourceAuthority<'a>,
    payload: CertifiedMonitorNativePayloadReceipt<'a>,
}

#[derive(Serialize)]
struct CertifiedMonitorNativeSourceAuthority<'a> {
    implementation: &'static str,
    before: CertifiedMonitorNativeSourceAuthorityPoint<'a>,
    after: CertifiedMonitorNativeSourceAuthorityPoint<'a>,
    stable_head: bool,
}

#[derive(Serialize)]
struct CertifiedMonitorNativeSourceAuthorityPoint<'a> {
    status: &'static str,
    head: &'a str,
    recursive_checkout_clean: bool,
}

#[derive(Serialize)]
struct CertifiedMonitorNativePayloadReceipt<'a> {
    evidence_directory: String,
    evidence_manifest_path: String,
    evidence_manifest_sha256: &'a str,
    evidence_manifest_entries: usize,
    identity_path: String,
    identity_sha256: &'a str,
    identity_schema: &'static str,
    stage2_sysroot: &'a str,
    stage2_tree_sha256: &'a str,
    trustc_sha256: &'a str,
    targo_sha256: &'a str,
    targo_trust_sha256: &'a str,
    trustd_sha256: &'a str,
    manifest_sha256: &'a str,
    lock_sha256: &'a str,
    trustc_commit: &'a str,
    targo_commit: &'a str,
    targo_trust_commit: &'a str,
    trustd_commit: &'a str,
}

pub(super) fn render_certified_monitor_native_authority_receipt(
    repo_root: &Path,
    authority_receipt_path: &Path,
    head: &str,
    payload: &ValidatedCertifiedMonitorPayload,
) -> Result<Vec<u8>, String> {
    let path_string = |path: &Path, label: &str| {
        path.to_str()
            .map(str::to_string)
            .ok_or_else(|| format!("{label} path is not valid UTF-8: {}", path.display()))
    };
    let receipt = CertifiedMonitorNativeAuthorityReceipt {
        schema: CERTIFIED_MONITOR_NATIVE_AUTHORITY_SCHEMA,
        status: "pass",
        result_scope: "source-and-payload-authority",
        source_authority: "native-controlled-git-before-and-after",
        head,
        repository_root: path_string(repo_root, "repository root")?,
        authority_receipt_path: path_string(authority_receipt_path, "authority receipt")?,
        authority: CertifiedMonitorNativeSourceAuthority {
            implementation: "trust.controlled-git/v1",
            before: CertifiedMonitorNativeSourceAuthorityPoint {
                status: "verified",
                head,
                recursive_checkout_clean: true,
            },
            after: CertifiedMonitorNativeSourceAuthorityPoint {
                status: "verified",
                head,
                recursive_checkout_clean: true,
            },
            stable_head: true,
        },
        payload: CertifiedMonitorNativePayloadReceipt {
            evidence_directory: path_string(
                &payload.evidence_directory,
                "payload evidence directory",
            )?,
            evidence_manifest_path: path_string(
                &payload.evidence_manifest,
                "payload evidence manifest",
            )?,
            evidence_manifest_sha256: &payload.evidence_manifest_sha256,
            evidence_manifest_entries: CERTIFIED_MONITOR_PAYLOAD_FILES.len(),
            identity_path: path_string(&payload.identity_path, "payload identity")?,
            identity_sha256: &payload.identity_sha256,
            identity_schema: CERTIFIED_MONITOR_PAYLOAD_IDENTITY_SCHEMA,
            stage2_sysroot: &payload.identity.stage2_sysroot,
            stage2_tree_sha256: &payload.identity.stage2_tree_sha256,
            trustc_sha256: &payload.identity.trustc_sha256,
            targo_sha256: &payload.identity.targo_sha256,
            targo_trust_sha256: &payload.identity.targo_trust_sha256,
            trustd_sha256: &payload.identity.trustd_sha256,
            manifest_sha256: &payload.identity.manifest_sha256,
            lock_sha256: &payload.identity.lock_sha256,
            trustc_commit: &payload.identity.trustc_commit,
            targo_commit: &payload.identity.targo_commit,
            targo_trust_commit: &payload.identity.targo_trust_commit,
            trustd_commit: &payload.identity.trustd_commit,
        },
    };
    let mut bytes = serde_json::to_vec_pretty(&receipt)
        .map_err(|error| format!("cannot serialize native authority receipt: {error}"))?;
    bytes.push(b'\n');
    if bytes.len() as u64 > CERTIFIED_MONITOR_MAX_IDENTITY_BYTES {
        return Err("native authority receipt exceeds its bounded size".to_string());
    }
    Ok(bytes)
}
